#!/usr/bin/env python3
"""Measure Lean requirement coverage by replaying an existing corpus (no fuzzing).

Build with ./build_cov.sh first.  From the repository root:
  harness/scripts/measure_spec_coverage.py --output out/spec-coverage
  harness/scripts/spec_coverage.py out/spec-coverage/init.json \
      ngtcp2=out/spec-coverage/endpoint_diff.json \
      cq=out/spec-coverage/quiche_diff.json gq=out/spec-coverage/gquiche_diff.json

Retains replay logs for signature comparison, and subtractable initialization
profiles. Uses existing inputs only; it does not classify reported differences.
"""
import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('out/spec-coverage'))
    parser.add_argument('--corpus', type=Path, default=Path('corpus/conn_trace'))
    parser.add_argument('engines', nargs='*', default=[
        'endpoint_diff', 'quiche_diff', 'gquiche_diff'])
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    files = sorted(str(p) for p in args.corpus.iterdir() if p.is_file())
    if not files:
        parser.error('corpus must contain at least one input')
    empty = args.output / 'empty-input'
    empty.write_bytes(b'')

    def profile(engine, name, inputs):
        binary = Path('out') / (engine + '_cov')
        raw = args.output / (name + '.profraw')
        data = args.output / (name + '.profdata')
        env = {**os.environ, 'ASAN_OPTIONS': 'detect_leaks=0',
               'LLVM_PROFILE_FILE': str(raw),
               'DIFF_OUT': str(args.output / 'artifacts')}
        # Measurement must not inherit injected sends or verbose trace options.
        for key in ('DIFF_SELFTEST', 'DIFF_SHOW', 'TRACE_SHOW', 'DIFF_ALL',
                    'DIFF_DIGEST', 'DIFF_FAIL_ON_MISMATCH'):
            env.pop(key, None)
        with (args.output / (name + '.log')).open('w') as log:
            subprocess.run([str(binary), '-runs=0', *inputs], env=env,
                           stdout=log, stderr=log, check=True)
        subprocess.run(['llvm-profdata', 'merge', '-sparse', str(raw),
                        '-o', str(data)], check=True)
        exported = json.loads(subprocess.check_output([
            'llvm-cov', 'export', '-skip-expansions', str(binary),
            '-instr-profile=' + str(data)]))
        functions = {}
        for unit in exported['data']:
            for fn in unit['functions']:
                functions[fn['name']] = [fn['count'], fn['filenames'][0]]
        (args.output / (name + '.json')).write_text(json.dumps(functions))
        print(f'{name}: {len(inputs)} existing inputs profiled', flush=True)

    profile(args.engines[0], 'init', [str(empty)])
    with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
        futures = [pool.submit(profile, engine, engine, files) for engine in args.engines]
        for future in futures:
            future.result()


if __name__ == '__main__':
    main()
