#!/usr/bin/env python3
"""Adversarial end-to-end audit of generic frontend, IR, Lean, and proof CLI.

The installed Crystal/Lean versions and environment are those documented in README.
"""
import ast
import os
import re
import tempfile
from pathlib import Path

from support import cr_array, cr_int, run, tool_paths

cli, lean, crystal = tool_paths()

def evaluate(cr_source, model, cases):
    crystal_code=cr_source+'''\ndef audit(label : String, & : -> Int32)\n  begin\n    puts "#{label}:ok:#{yield}"\n  rescue ex\n    puts "#{label}:err:#{ex.class}"\n  end\nend\n'''
    lean_code=model+'''\ndef auditResult (label : String) (x : Except CrystalLeanIR.Error CrystalLeanIR.Value) : String :=\n  match x with\n  | .ok (.i32 n) => s!"{label}:ok:{n}"\n  | .error .divisionByZero => s!"{label}:err:DivisionByZeroError"\n  | .error .argumentError => s!"{label}:err:ArgumentError"\n  | .error .overflow => s!"{label}:err:OverflowError"\n  | .error .indexOutOfBounds => s!"{label}:err:IndexError"\n  | .error .outOfFuel => s!"{label}:err:outOfFuel"\n  | _ => s!"{label}:unexpected"\n'''
    for num,(cr_expr,lean_expr) in enumerate(cases):
        crystal_code+=f'audit("{num}") {{ {cr_expr} }}\n'
        lean_code+=f'#eval auditResult "{num}" ({lean_expr})\n'
    with tempfile.TemporaryDirectory(prefix='crystal-lean-eval-') as td:
        t=Path(td)
        (t/'check.cr').write_text(crystal_code)
        (t/'Check.lean').write_text(lean_code)
        actual=run([crystal,'run',t/'check.cr']).stdout.splitlines()
        modeled=[ast.literal_eval(line) for line in run([lean,t/'Check.lean']).stdout.splitlines()]
        if actual != modeled:
            raise AssertionError(f'Crystal/Lean mismatch\nCrystal: {actual}\nLean: {modeled}')
    return len(cases)

pairs=[(5,3),(5,-3),(-5,3),(-5,-3),(1,0),(-2147483648,-1),(-2147483648,1),
       (2147483647,1),(2147483647,-1),(2147483647,2)]
indices=[([],i) for i in (-2147483648,-1,0,1,2147483647)]
indices += [([10,20,30],i) for i in (-2147483648,-4,-3,-2,-1,0,1,2,3,2147483647)]
with tempfile.TemporaryDirectory(prefix='crystal-lean-e2e-') as td:
    tmp=Path(td)
    source=tmp/'function input; secure.cr'
    output=tmp/'out.lean'
    for op,name in [('//','quotient'),('%','modulus')]:
        cr=f'def {name}(a : Int32, b : Int32) : Int32\n  a {op} b\nend\n'
        source.write_text(cr)
        result=run([cli,'translate',source])
        count=evaluate(cr,result.stdout,[(f'{name}({cr_int(a)}, {cr_int(b)})',f'crystalProgram 100 ({a}) ({b})') for a,b in pairs])
        print(f'PASS: generic {op} generated from AST, {count} four-sign/zero/boundary cases')

    name='lookup_any_name'
    cr=f'def {name}(xs : Array(Int32), i : Int32) : Int32\n  xs[i]\nend\n'
    source.write_text(cr)
    model=run([cli,'translate',source]).stdout
    count=evaluate(cr,model,[(f'{name}({cr_array(xs)}, {cr_int(i)})',
                    f'crystalProgram 100 #[{", ".join(map(str,xs))}] ({i})') for xs,i in indices])
    print(f'PASS: generic array lookup {count} empty/negative/boundary/OOB cases')

    # Function identifiers may differ freely: they must never decide which
    # algorithm-specific Lean implementation is emitted.
    source.write_text('def alpha_name(x : Int32) : Int32\n  if x < 0\n    0\n  else\n    x\n  end\nend\n')
    alpha=run([cli,'translate',source]).stdout
    source.write_text(source.read_text().replace('alpha_name','completely_different'))
    renamed=run([cli,'translate',source]).stdout
    strip_comments=lambda text: re.sub(r'^-- Generated from Crystal method .*$', '', text, flags=re.M)
    if strip_comments(alpha)!=strip_comments(renamed):
        raise AssertionError('renaming the method unexpectedly changed generic model')
    inspected=run([cli,'inspect',source]).stdout
    if 'Intermediate representation:' not in inspected or 'completely_different' not in inspected:
        raise AssertionError('inspect did not expose the generic typed method and IR')
    run([cli,'translate',source,'-o',output])
    if output.read_text()!=renamed:
        raise AssertionError('translate -o did not preserve generated model')
    print('PASS: arbitrary function name, generic IR inspection and -o output')

    original = source.read_text()
    symlink = tmp/'source-symlink.cr'
    hardlink = tmp/'source-hardlink.cr'
    symlink.symlink_to(source)
    os.link(source, hardlink)
    for destination in (source, symlink, hardlink):
        run([cli, 'translate', source, '-o', destination], ok=False)
        if source.read_text() != original:
            raise AssertionError(f'translate overwrote input via {destination}')
    print('PASS: output cannot overwrite input through a path, symlink, or hard link')

    loop='''def count_different(n : Int32) : Int32
  i = 0
  while i < n
    i = i + 1
  end
  i
end
'''
    source.write_text(loop)
    baseline=run([cli,'translate',source]).stdout
    count=evaluate(loop,baseline,[(f'count_different({cr_int(n)})',f'crystalProgram 100 ({n})') for n in (-3,0,1,3,6)])
    changed=loop.replace('i = i + 1','i = i + 2')
    source.write_text(changed)
    mutated=run([cli,'translate',source]).stdout
    if mutated == baseline:
        raise AssertionError('the source mutation did not change generated IR/model')
    evaluate(changed,mutated,[(f'count_different({cr_int(3)})','crystalProgram 100 3')])
    print(f'PASS: generic loop {count} normal cases, mutation follows actual source')

    early='''def conditional_exit(a : Int32, b : Int32) : Int32
  if a > 0
    return a
  end
  a // b
end
'''
    source.write_text(early)
    early_model=run([cli,'translate',source]).stdout
    early_cases=[(1,0),(7,-3),(0,1),(-5,3),(-5,0)]
    count=evaluate(early,early_model,[(f'conditional_exit({cr_int(a)}, {cr_int(b)})',
                       f'crystalProgram 100 ({a}) ({b})') for a,b in early_cases])
    print(f'PASS: {count} real early-return and error evaluation-order cases')

    # Invalid semantics must fail closed before Lean output is presented.
    for bad in ['def f(x : Int32, y : Int32) : Int32\n  x / y\nend\n',
                'def f(x : Int32, y : Int32) : Int32\n  x &+ y\nend\n',
                'def f(x : Int32) : Int32\n  puts x\n  x\nend\n',
                'def f(xs : Array(Int32)) : Int32\n  xs[0] = 3\n  0\nend\n',
                'def f(x : Int32) : Int32\n  if x\n    1\n  else\n    0\n  end\nend\n',
                'def f(x : Bool, y : Bool) : Bool\n  x && y\nend\n',
                'def f(x : Bool, y : Bool) : Bool\n  x || y\nend\n',
                'def f(x : Bool) : Int32\n  if x\n    y = 1\n  end\n  y\nend\n']:
        source.write_text(bad)
        run([cli,'translate',source],ok=False)
    print('PASS: unsupported float division, wrapping, I/O, mutation, truthiness, boolean short-circuit operators, and conditionally uninitialized local rejected')

print('All CLI integration checks passed.')
