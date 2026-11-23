"""Shared tools for the standalone integration tests."""

import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def tool_paths():
    if len(sys.argv) != 4:
        raise SystemExit(f'usage: {sys.argv[0]} CLI LEAN CRYSTAL')
    cli, lean, crystal = (str(Path(path).absolute()) for path in sys.argv[1:])
    os.environ['CRYSTAL'] = crystal
    os.environ.pop('CRYSTAL_PATH', None)
    return cli, lean, crystal


def run(command, *, ok=True):
    args = [str(arg) for arg in command]
    result = subprocess.run(args, text=True, capture_output=True, timeout=180)
    if (result.returncode == 0) != ok:
        raise AssertionError(
            f'{args!r} exited with {result.returncode}\n'
            f'stdout:\n{result.stdout}\nstderr:\n{result.stderr}'
        )
    return result


def cr_int(value):
    return 'Int32::MIN' if value == -(2**31) else f'{value}_i32'


def cr_array(values):
    return '[' + ', '.join(map(cr_int, values)) + ']' if values else '([] of Int32)'


def lean_array(values):
    return '#[' + ', '.join(map(str, values)) + ']'
