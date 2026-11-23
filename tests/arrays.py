#!/usr/bin/env python3
"""Compare actual Crystal array writes against generated Lean models.

These finite tests do not prove either sorting or translation correctness.
"""
import ast
import json
import random
import tempfile
from pathlib import Path

from support import ROOT, cr_array, cr_int, lean_array, run, tool_paths

cli, lean, crystal = tool_paths()

def parse_outcome(line):
    if line.startswith('ok:'):
        return ('ok', json.loads(line[3:]))
    if line.startswith('err:'):
        return ('err', line[4:])
    raise AssertionError(f'unexpected result (including out-of-fuel): {line}')


fixtures = {
    'write_at': '''def write_at(xs : Array(Int32), index : Int32, value : Int32) : Array(Int32)
  xs[index] = value
  xs
end
''',
    'write_expr': '''def write_expr(xs : Array(Int32), left : Int32, right : Int32) : Array(Int32)
  xs[10 // left] = 10 // right
  return xs
end
''',
    'write_order': '''def write_order(xs : Array(Int32), index : Int32, denominator : Int32) : Array(Int32)
  xs[index + 1] = 10 // denominator
  xs
end
''',
    'reverse_in_place': '''def reverse_in_place(xs : Array(Int32)) : Array(Int32)
  i = 0
  j = xs.size - 1
  while i < j
    temp = xs[i]
    xs[i] = xs[j]
    xs[j] = temp
    i = i + 1
    j = j - 1
  end
  xs
end
''',
}
rng = random.Random(20261123)
arrays = [[], [1], [3, 3, 3], [3, 1, 2], [-(2**31), 2**31-1],
          [2**31-1, -(2**31), 0, 0]]
arrays += [[rng.randrange(-5, 6) for _ in range(rng.randrange(0, 8))] for _ in range(24)]
cases = {
    'bubble_sort': [(xs,) for xs in arrays],
    'reverse_in_place': [(xs,) for xs in arrays],
    'write_at': [(xs, i, 99) for xs in ([], [10], [10, 20, 30])
                 for i in (-(2**31), -4, -3, -2, -1, 0, 1, 2, 3, 2**31-1)],
    # In particular, both an invalid index and a failing RHS must report the
    # RHS error: Crystal checks bounds inside []= after evaluating arguments.
    'write_expr': [([1, 2], a, b) for a, b in
                   [(0, 0), (1, 0), (1, 1), (10, 0), (10, 1), (-10, 1)]],
    # Distinguish failure while evaluating the index from a failing RHS.
    'write_order': [([1, 2], i, d) for i, d in
                    [(2**31-1, 0), (0, 0), (3, 0), (3, 1), (0, 1)]],
}

lean_display = '''
def displayArrayResult (r : Except CrystalLeanIR.Error CrystalLeanIR.Value) : String :=
  match r with
  | .ok (.array xs) => "ok:" ++ toString xs.toList
  | .error .indexOutOfBounds => "err:IndexError"
  | .error .divisionByZero => "err:DivisionByZeroError"
  | .error .argumentError => "err:ArgumentError"
  | .error .overflow => "err:OverflowError"
  | .error .outOfFuel => "unexpected:outOfFuel"
  | _ => "unexpected:other"
'''

with tempfile.TemporaryDirectory(prefix='crystal-lean-array-diff-') as tmp:
    tmp = Path(tmp)
    sources = {'bubble_sort': ROOT /  'examples/bubble_sort.cr'}
    for name, source in fixtures.items():
        path = tmp / f'{name}.cr'
        path.write_text(source, encoding='utf-8')
        sources[name] = path

    crystal_program = '''require "json"
def show(& : -> Array(Int32))
  begin
    puts "ok:#{yield.to_json}"
  rescue ex
    puts "err:#{ex.class}"
  end
end
'''
    crystal_program += '\n'.join(path.read_text(encoding='utf-8') for path in sources.values())
    labels = []
    for name, examples in cases.items():
        for xs, *args in examples:
            call_args = ', '.join([cr_array(xs)] + list(map(cr_int, args)))
            crystal_program += f'\nshow {{ {name}({call_args}) }}'
            labels.append((name, xs, args))
    crystal_file = tmp / 'actual.cr'
    crystal_file.write_text(crystal_program + '\n', encoding='utf-8')
    actual_lines = run([crystal, 'run', crystal_file]).stdout.splitlines()
    if len(actual_lines) != len(labels):
        raise AssertionError(f'wrong Crystal result count: {len(actual_lines)} vs {len(labels)}')
    actual = [parse_outcome(line) for line in actual_lines]

    offset = 0
    for name, examples in cases.items():
        model = run([cli, 'translate', sources[name]]).stdout
        if not model.startswith('import Std'):
            raise AssertionError(f'unexpected model for {name}')
        evals = []
        for xs, *args in examples:
            call_args = ' '.join([lean_array(xs)] + [f'({x})' for x in args])
            evals.append(f'#eval displayArrayResult (crystalProgram 1024 {call_args})')
        model_file = tmp / f'{name}.lean'
        model_file.write_text(model + lean_display + '\n'.join(evals) + '\n', encoding='utf-8')
        lines = run([lean, model_file]).stdout.splitlines()
        if len(lines) != len(examples):
            raise AssertionError(f'wrong Lean result count for {name}: {lines!r}')
        for n, (case, line) in enumerate(zip(examples, lines)):
            got = parse_outcome(ast.literal_eval(line))
            expected = actual[offset + n]
            if got != expected:
                raise AssertionError(f'{name}{case}: Lean={got}, Crystal={expected}')
            if name == 'bubble_sort' and got != ('ok', sorted(case[0])):
                raise AssertionError(f'bubble_sort failed its concrete oracle: {case!r}, {got!r}')
            if name == 'reverse_in_place' and got != ('ok', list(reversed(case[0]))):
                raise AssertionError(f'reverse failed its concrete oracle: {case!r}, {got!r}')
        offset += len(examples)
        print(f'PASS: {name}: {len(examples)} Crystal/Lean outcomes')
print('Finite differential tests do not prove program or translation correctness.')
