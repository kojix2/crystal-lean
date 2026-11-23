#!/usr/bin/env python3
"""Differential audit of the generic Lean runtime, plus proof-reduction smoke tests.

Crystal expressions are evaluated dynamically, not folded by either compiler.
"""
import ast
import re
import tempfile
from pathlib import Path

from support import ROOT, cr_array, cr_int, lean_array, run, tool_paths

_cli, lean, crystal = tool_paths()

runtime = (ROOT / 'src/crystal_lean/lean_runtime.lean').read_text()
for forbidden in ('partial', 'sorry', 'admit', 'axiom', 'unsafe', 'native_decide'):
    if re.search(r'\b' + forbidden + r'\b', runtime):
        raise SystemExit(f'review required: Lean runtime mentions {forbidden}')

# Exercise floors with all sign pairs, zero divisor, corner overflow, boundaries
# on all 3 basic arithmetic operations. Values are all valid Crystal Int32s.
pairs = [(5,3),(5,-3),(-5,3),(-5,-3),(1,0),(0,0),
         (-2147483648,-1),(-2147483648,1),(-2147483648,2),
         (2147483647,1),(2147483647,-1),(2147483647,2),(-2147483648,-2147483648)]
indices=[([],i) for i in (-2147483648,-1,0,1,2147483647)]
indices += [([10,20,30],i) for i in (-2147483648,-4,-3,-2,-1,0,1,2,3,2147483647)]

crystal_program = '''\ndef show(label : String, & : -> Int32)\n  begin\n    puts "#{label}:ok:#{yield}"\n  rescue ex\n    puts "#{label}:err:#{ex.class}"\n  end\nend\n'''
lean_program = '''\nopen CrystalLeanIR\ndef auditResult (label : String) (x : Except Error Value) : String :=\n  match x with\n  | .ok (.i32 n) => s!"{label}:ok:{n}"\n  | .error .divisionByZero => s!"{label}:err:DivisionByZeroError"\n  | .error .argumentError => s!"{label}:err:ArgumentError"\n  | .error .overflow => s!"{label}:err:OverflowError"\n  | .error .indexOutOfBounds => s!"{label}:err:IndexError"\n  | _ => s!"{label}:unexpected"\n'''
ops=[('+','add'),('-','sub'),('*','mul'),('//','floorDiv'),('%','mod')]
for num,(a,b) in enumerate(pairs):
    for symbol,lean_op in ops:
        label=f'{num}:{lean_op}'
        crystal_program+=f'show("{label}") {{ a = {cr_int(a)}; b = {cr_int(b)}; a {symbol} b }}\n'
        lean_program+=f'#eval auditResult "{label}" (binary .{lean_op} (.i32 ({a})) (.i32 ({b})))\n'
for num,(xs,i) in enumerate(indices):
    label=f'idx{num}'
    crystal_program+=f'show("{label}") {{ xs = {cr_array(xs)}; i = {cr_int(i)}; xs[i] }}\n'
    lean_program+=f'#eval auditResult "{label}" (eval [("xs", .array {lean_array(xs)})] (.arrayGet (.variable "xs") (.intLit ({i}))))\n'

# These reduce under the kernel to checked propositions; exhaustion remains
# distinguishable from termination and is not an alleged Crystal exception.
lean_program+='''\ndef auditLoop : Stmt := .seq [
  .assign "x" (.intLit 0),
  .whileLoop (.binary .lt (.variable "x") (.intLit 3))
    (.assign "x" (.binary .add (.variable "x") (.intLit 1))),
  .returnValue (.variable "x")]
example : run 0 auditLoop [] = .error .outOfFuel := by rfl
example : run 2 auditLoop [] = .error .outOfFuel := by rfl
example : run 30 auditLoop [] = .ok (.i32 3) := by rfl
example : run 10 (.whileLoop (.boolLit true) (.seq [])) [] = .error .outOfFuel := by rfl
example : run 20 (.seq [.ifElse (.boolLit true) (.returnValue (.intLit 7)) (.seq []),
  .returnValue (.binary .add (.intLit 2147483647) (.intLit 1))]) [] = .ok (.i32 7) := by rfl
example : run 10 (.seq [.assign "x" (.intLit 0), .returnValue (.variable "x")]) [("x", .i32 9)] = .ok (.i32 0) := by rfl
example : execute 10 (.seq [.assign "x" (.intLit 1), .assign "x" (.intLit 2),
  .arraySet "xs" (.intLit 0) (.variable "x")]) [("xs", .array #[0])] =
  .ok (.next [("xs", .array #[2]), ("x", .i32 2)]) := by rfl
example : eval [] (.unary .not (.boolLit false)) = .ok (.bool true) := by rfl
example : eval [] (.binary .eq (.boolLit true) (.boolLit false)) = .ok (.bool false) := by rfl
example : eval [] (.binary .add (.binary .add (.intLit 2147483647) (.intLit 1))
  (.binary .floorDiv (.intLit 1) (.intLit 0))) = .error .overflow := by rfl
example : eval [] (.binary .add (.binary .floorDiv (.intLit 1) (.intLit 0))
  (.binary .add (.intLit 2147483647) (.intLit 1))) = .error .divisionByZero := by rfl
example : run 15 (.ifElse (.boolLit false) (.returnValue (.binary .floorDiv (.intLit 1) (.intLit 0)))
  (.returnValue (.intLit 7))) [] = .ok (.i32 7) := by rfl
'''
with tempfile.TemporaryDirectory(prefix='crystal-lean-runtime-audit-') as temp:
    t=Path(temp)
    (t/'audit.cr').write_text(crystal_program)
    (t/'Audit.lean').write_text(runtime+'\n'+lean_program)
    crystal_out=run([crystal,'run',str(t/'audit.cr')]).stdout.splitlines()
    lean_out=run([lean,str(t/'Audit.lean')]).stdout.splitlines()
    lean_values=[ast.literal_eval(line) for line in lean_out]
    if crystal_out != lean_values:
        for i,(a,b) in enumerate(zip(crystal_out,lean_values)):
            if a!=b:
                print(f'MISMATCH {i}: Crystal={a!r}; Lean={b!r}')
        raise SystemExit(f'output mismatch: Crystal {len(crystal_out)} lines vs Lean {len(lean_values)} lines')
    print(f'PASS: {len(crystal_out)} Crystal/Lean boundary evaluations and 12 kernel-checked runtime cases')
