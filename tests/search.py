#!/usr/bin/env python3
"""Evaluate two differently structured generic binary searches in both languages.

This is differential testing, NOT a proof of binary-search correctness or of
Crystal-to-Lean semantic preservation. Only sorted cases have a search oracle.
"""
import ast
import random
import tempfile
from pathlib import Path

from support import ROOT, cr_array, cr_int, lean_array, run, tool_paths

cli, lean, crystal = tool_paths()

sources = [ROOT /  'examples/binary_search_early_return.cr',
           ROOT /  'examples/binary_search_lower_bound.cr']


def lean_result(s):
    prefix = 'Except.ok (CrystalLeanIR.Value.i32 '
    if not s.startswith(prefix) or not s.endswith(')'):
        raise AssertionError(f'model returned an exception or ran out of fuel: {s}')
    return ast.literal_eval(s[len(prefix):-1])


rng = random.Random(20261123)
cases = [([], 0), ([1], 1), ([1], 2), ([3, 3, 3, 3], 3),
         ([-2**31, 2**31-1], -2**31), ([-2**31, 2**31-1], 2**31-1),
         ([3, 1, 2], 3), ([3, 1, 2], 1)]
cases += [(sorted(rng.randrange(-8, 9) for _ in range(rng.randrange(0, 24))),
           rng.randrange(-10, 11)) for _ in range(32)]

with tempfile.TemporaryDirectory(prefix='crystal-lean-generic-search-') as d:
    temp = Path(d)
    # The real source files are compiled together and run; no manual search
    # reimplementation is used to claim Crystal's behavior.
    cr_file = temp / 'check.cr'
    crystal_src = '\n'.join(path.read_text(encoding='utf-8') for path in sources)
    for xs, key in cases:
        crystal_src += f'\nputs locate_early({cr_array(xs)}, {cr_int(key)})'
        crystal_src += f'\nputs find_first({cr_array(xs)}, {cr_int(key)})'
    cr_file.write_text(crystal_src + '\n', encoding='utf-8')
    crystal_lines = run([crystal, 'run', cr_file]).stdout.splitlines()
    if len(crystal_lines) != 2 * len(cases):
        raise AssertionError(f'unexpected Crystal output: {crystal_lines!r}')
    actual = [[int(crystal_lines[2*i + j]) for j in range(2)] for i in range(len(cases))]

    for j, source in enumerate(sources):
        model = run([cli, 'translate', source]).stdout
        if not model.startswith('import Std'):
            raise AssertionError(f'unexpected generated model: {model[:100]!r}')
        ln_file = temp / f'Model{j}.lean'
        lines = [f'#eval crystalProgram 256 {lean_array(xs)} ({key})' for xs, key in cases]
        ln_file.write_text(model + '\n' + '\n'.join(lines) + '\n', encoding='utf-8')
        results = run([lean, ln_file]).stdout.splitlines()
        if len(results) != len(cases):
            raise AssertionError(f'{source}: wrong Lean result count: {results!r}')
        for i, ((xs, key), line) in enumerate(zip(cases, results)):
            got = lean_result(line)
            if got != actual[i][j]:
                raise AssertionError(f'{source.name}, {xs!r}, {key}: Lean={got}, Crystal={actual[i][j]}')
            if xs == sorted(xs):
                if (got == -1) != (key not in xs):
                    raise AssertionError(f'bad sorted lookup {source.name}, {xs!r}, {key}, {got}')
                if got != -1 and (got < 0 or got >= len(xs) or xs[got] != key):
                    raise AssertionError(f'bad index {source.name}, {xs!r}, {key}, {got}')
                if j == 1 and got != -1 and got != xs.index(key):
                    raise AssertionError(f'lower bound not first occurrence: {xs!r}, {key}, {got}')
        print(f'PASS: {source.name}: {len(cases)} matching Crystal/Lean outcomes')
print('This differential test does not prove binary-search correctness.')
