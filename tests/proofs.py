#!/usr/bin/env python3
"""Test generic source→model→user-proof wiring using actual Crystal and Lean.

The Crystal source-to-Lean correspondence remains an unproved assumption.
"""
import tempfile
from pathlib import Path

from support import ROOT, run, tool_paths

cli, lean, crystal = tool_paths()

base = (ROOT /  'examples/clamp.cr').read_text(encoding='utf-8')
proof = ROOT /  'proofs/clamp_correct.lean'
loop_proof = ROOT /  'proofs/while_exit_condition.lean'


def run_cli(*args, expected=True):
    return run([cli, *args], ok=expected)


with tempfile.TemporaryDirectory(prefix='crystal-lean-proof-test-') as d:
    tmp = Path(d)
    source = tmp / 'function source.cr'
    source.write_text(base, encoding='utf-8')
    opts = ['--proof', proof, '--theorem', 'clamp_correct', '--lean', lean]
    result = run_cli('verify', source, *opts)
    if 'clamp_correct' not in result.stdout or 'sorryAx' in result.stdout:
        raise AssertionError('Missing axiom report or sorryAx present: ' + result.stdout)
    print('PASS: every Int32 input satisfies generated clamp specification')

    mutant = base.replace('    100\n', '    99\n', 1)
    if mutant == base:
        raise AssertionError('clamp mutation did not apply')
    source.write_text(mutant, encoding='utf-8')
    run_cli('translate', source)
    run_cli('verify', source, *opts, expected=False)
    print('PASS: same theorem rejects changed generated function')

    source.write_text(base, encoding='utf-8')
    run_cli('verify', source, '--proof', loop_proof, '--theorem', 'while_exit_condition', '--lean', lean)
    print('PASS: reusable normal-while-exit lemma checks against runtime')
    count_source = ROOT /  'examples/count_up.cr'
    count_proof = ROOT /  'proofs/count_up_cases.lean'
    run_cli('verify', count_source, '--proof', count_proof, '--theorem', 'count_up_nonpositive', '--lean', lean)
    run_cli('verify', count_source, '--proof', count_proof, '--theorem', 'count_up_three', '--lean', lean)
    print('PASS: count-up nonpositive inputs and a three-iteration execution')
    run_cli('verify', source, '--proof', proof, '--theorem', 'missing_theorem', '--lean', lean, expected=False)
    print('PASS: missing named theorem rejected')

    non_proof = tmp / 'non_proof.lean'
    non_proof.write_text('def not_a_proof : Nat := 3\n', encoding='utf-8')
    result = run_cli('verify', source, '--proof', non_proof, '--theorem', 'not_a_proof', '--lean', lean, expected=False)
    if 'does not have a proposition type' not in result.stdout + result.stderr:
        raise AssertionError('missing explanation that the declaration is not a proposition')
    print('PASS: non-Prop declaration rejected as a theorem')

    sorry = tmp / 'unproved.lean'
    sorry.write_text('theorem missing_proof : False := by\n  sorry\n', encoding='utf-8')
    run_cli('verify', source, '--proof', sorry, '--theorem', 'missing_proof', '--lean', lean, expected=False)
    print('PASS: named theorem depending on sorryAx rejected')

    unrelated = tmp / 'unrelated.lean'
    unrelated.write_text(
        'import Std\n'
        'theorem unfinished : False := by sorry\n'
        '#print axioms unfinished\n'
        'theorem unrelated : True := by trivial\n',
        encoding='utf-8',
    )
    result = run_cli('verify', source, '--proof', unrelated, '--theorem', 'unrelated', '--lean', lean)
    if 'does not establish' not in result.stdout or 'uses the generated model' not in result.stdout:
        raise AssertionError('missing explicit warning about unrelated declarations')
    print('PASS: unrelated axiom output does not affect the selected theorem, and its scope is reported')

    declared_axiom = tmp / 'assumption.lean'
    declared_axiom.write_text('axiom assumed_false : False\n', encoding='utf-8')
    result = run_cli('verify', source, '--proof', declared_axiom, '--theorem', 'assumed_false', '--lean', lean)
    if 'assumed_false' not in result.stdout or 'depends on axioms' not in result.stdout:
        raise AssertionError('custom axiom dependency not shown')
    print('PASS: explicit axiom exposed as assumption rather than concealed')

    contract = tmp / 'spec.lean'
    contract.write_text(
        'open CrystalLeanIR\n'
        'def ClampSpec : Prop := ∀ x : Int, minimum ≤ x ∧ x ≤ maximum →\n'
        '  crystalProgram 20 x = .ok (.i32 (if x < 0 then 0 else if x > 100 then 100 else x))\n',
        encoding='utf-8',
    )
    strict = ['--contract', contract, '--statement', 'ClampSpec']
    result = run_cli('verify', source, *opts, *strict)
    assert 'Crystal Lean proof gate: accepted' in result.stdout
    print('PASS: independent clamp contract and theorem have the same kernel type')

    result = run_cli('verify', source, '--proof', unrelated, '--theorem', 'unrelated',
                 '--lean', lean, *strict, expected=False)
    assert 'theorem does not state the expected contract' in result.stdout + result.stderr

    declared_axiom.write_text(
        'axiom asserted_clamp : ClampSpec\n'
        'theorem false_clamp : ClampSpec := asserted_clamp\n',
        encoding='utf-8',
    )
    result = run_cli('verify', source, '--proof', declared_axiom, '--theorem', 'false_clamp',
                 '--lean', lean, *strict, expected=False)
    assert 'unapproved axioms' in result.stdout + result.stderr

    unrelated.write_text(
        'def OutsiderSpec : Prop := crystalProgram 0 0 = crystalProgram 0 0\n'
        'theorem unrelated : OutsiderSpec := rfl\n', encoding='utf-8',
    )
    result = run_cli('verify', source, '--proof', unrelated, '--theorem', 'unrelated',
                 '--lean', lean, '--contract', contract, '--statement', 'OutsiderSpec', expected=False)
    assert 'contract must be defined in CrystalLeanContract' in result.stdout + result.stderr
    print('PASS: wrong theorem, additional axioms, and a proof-supplied contract are rejected')

    generated = tmp / 'Generated.lean'
    run_cli('translate', source, '-o', generated, '--check', expected=False)
    run_cli('translate', source, '-o', generated)
    run_cli('translate', source, '-o', generated, '--check')
    original = generated.read_bytes()
    source.write_text(mutant, encoding='utf-8')
    run_cli('translate', source, '-o', generated, '--check', expected=False)
    assert generated.read_bytes() == original
    print('PASS: stale generated model rejected without writing')

    count_contract = ROOT /  'proofs/count_up_total_contract.lean'
    run_cli('verify', count_source, '--lean', lean,
        '--proof', ROOT /  'proofs/count_up_total.lean', '--theorem', 'count_up_total',
        '--contract', count_contract, '--statement', 'CountUpContract.correct')
    print('PASS: generated count-up terminates for every nonnegative Int32 input')

    sort_source = ROOT /  'examples/bubble_sort.cr'
    sort_opts = ['--lean', lean,
                 '--proof', ROOT /  'proofs/bubble_sort_correct.lean',
                 '--theorem', 'bubble_sort_correct',
                 '--contract', ROOT /  'proofs/bubble_sort_contract.lean',
                 '--statement', 'BubbleSortContract.correct']
    run_cli('verify', sort_source, *sort_opts)
    text = sort_source.read_text(encoding='utf-8')
    swapped_comparison = text.replace('xs[position] >', 'xs[position] <', 1)
    assert swapped_comparison != text
    source.write_text(swapped_comparison, encoding='utf-8')
    run_cli('translate', source)
    rejected = run_cli('verify', source, *sort_opts, expected=False)
    assert 'Lean rejected CrystalLeanProof' in rejected.stdout + rejected.stderr
    print('PASS: generated bubble sort returns a sorted permutation for all valid inputs')
    print('PASS: reversing the sort comparison still translates and breaks the proof')
print('All generic proof integration checks passed.')
