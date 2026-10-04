#!/usr/bin/env python3
"""Compare real Python host decisions with Lean's host model using mock launches.

Run under the project's single-worker memory/CPU limits after compiling
PoissonPTX.HostScheduleTest. This does not execute a GPU or assert conformance.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from test_poisson_host import python_result, scenarios

ROOT = Path(__file__).resolve().parents[1]
INTEGRATION = ROOT / 'integration/torchlean'


def check(output):
    paths = [Path(__file__).resolve(), ROOT/'hardware/test_poisson_host.py',
             ROOT/'hardware/poisson_runtime.py', INTEGRATION/'lean-toolchain',
             INTEGRATION/'PoissonPTX/HostSchedule.lean', INTEGRATION/'PoissonPTX/HostExecution.lean',
             INTEGRATION/'PoissonPTX/HostScheduleEval.lean', INTEGRATION/'PoissonPTX/HostScheduleTest.lean']
    hashes = lambda: {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    before = hashes()
    cases = scenarios()
    expected = [python_result(c) for c in cases]
    with tempfile.TemporaryDirectory(prefix='poisson-host-') as directory:
        directory = Path(directory)
        inputs = directory/'cases.json'
        inputs.write_text(json.dumps(cases))
        driver = directory/'Check.lean'
        # The path is a local temporary filename, encoded as a Lean string.
        driver.write_text('import PoissonPTX.HostScheduleTest\n'
            'open Lean PtxTorchLean.Poisson.PTX.Host.Test\n'
            '#eval do\n'
            f'  let text ← IO.FS.readFile {json.dumps(str(inputs))}\n'
            '  let cases ← IO.ofExcept (Json.parse text >>= Json.getArr?)\n'
            '  let results ← IO.ofExcept (cases.mapM runCase)\n'
            '  IO.println (toJson results).compress\n')
        completed = subprocess.run(['lake', '--no-cache', 'env', 'lean', '-j1', '-M5120', driver],
                                   cwd=INTEGRATION, capture_output=True, text=True, timeout=120, check=True)
        if completed.stderr:
            raise AssertionError(completed.stderr)
        actual = json.loads(completed.stdout)
    if len(actual) != len(expected):
        raise AssertionError('wrong number of model results')
    for i, (lean, python) in enumerate(zip(actual, expected, strict=True)):
        if lean != python:
            raise AssertionError(dict(case=i, input=cases[i], lean=lean, python=python))
        if len(lean['launches']) > 6+17*cases[i]['maximum']:
            raise AssertionError('launch bound violated')
    if hashes() != before:
        raise AssertionError('sources changed during comparison')
    report = dict(status='pass', cases=len(cases), source_sha256=before,
                  claim='Differential host control with mocked launches; not kernel or hardware verification.',
                  compared=['launch order', 'iteration count', 'stop reason', 'restart count',
                            'residual words', 'check positions and flags'])
    output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(status='pass', cases=len(cases), receipt=str(output))))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    check(parser.parse_args().output)
