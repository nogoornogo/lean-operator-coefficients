#!/usr/bin/env python3
"""Linux-only bounded diagnostic runner; never a theorem premise.

Usage: python3 tools/exact-rank/kernel-probe.py [--build] INPUT OUTPUT.log
With --build, INPUT is one Lake module; otherwise it is a Lean source path.
Build imported modules first. Measures the Lake/Lean process group's sampled
RSS and interrupts at 16 GiB or 300 seconds by default without changing Lean
options or process resource limits. Optional smaller budgets and a host
MemAvailable reserve support structural proof builds. A sampled peak is not
an exact maximum RSS, and polling is not a hard memory limit.
"""
import argparse
import os
import signal
import subprocess
import sys
import time


def group_rss_kib(group_id):
    total = 0
    for entry in os.scandir('/proc'):
        if not entry.name.isdigit():
            continue
        try:
            with open(entry.path + '/stat') as stream:
                fields = stream.read().rsplit(')', 1)[1].split()
            if int(fields[2]) != group_id:
                continue
            with open(entry.path + '/status') as stream:
                lines = stream.read().splitlines()
            total += next(int(x.split()[1]) for x in lines if x.startswith('VmRSS:'))
        except (OSError, ValueError, IndexError, StopIteration):
            continue
    return total


def interrupt_group(process, sig):
    try:
        os.killpg(process.pid, sig)
    except ProcessLookupError:
        pass


def available_kib():
    with open('/proc/meminfo') as stream:
        for line in stream:
            if line.startswith('MemAvailable:'):
                return int(line.split()[1])
    raise RuntimeError('MemAvailable is unavailable; refusing unmonitored execution')


def positive(value):
    number = float(value)
    if not 0 < number < float('inf'):
        raise argparse.ArgumentTypeError('expected a positive finite number')
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true', help='monitor lake build MODULE')
    parser.add_argument('--rss-limit-gib', type=positive, default=16,
                        help='sampled process-group RSS limit (default: 16)')
    parser.add_argument('--min-available-gib', type=positive,
                        help='interrupt below this host MemAvailable reserve')
    parser.add_argument('--timeout-seconds', type=positive, default=300,
                        help='wall-clock stopping budget (default: 300)')
    parser.add_argument('--require-cached', action='append', default=[], metavar='MODULE',
                        help='refuse execution unless lake --no-build build MODULE passes')
    parser.add_argument('input')
    parser.add_argument('log')
    args = parser.parse_args()
    reserve = args.min_available_gib * 1024 * 1024 if args.min_available_gib else 0
    if reserve and available_kib() < reserve:
        print('refusing launch: host available memory is below the requested reserve', flush=True)
        return 1
    command = ['lake', 'build', args.input] if args.build else ['lake', 'env', 'lean', args.input]
    start = time.monotonic()
    peak, stopped = 0, False
    with open(args.log, 'w') as log:
        for module in args.require_cached:
            try:
                check = subprocess.run(['lake', '--no-build', 'build', module],
                                       stdout=log, stderr=log, timeout=args.timeout_seconds)
            except subprocess.TimeoutExpired:
                print(f'refusing launch: cache precondition timed out for {module}', flush=True)
                return 1
            if check.returncode:
                print(f'refusing launch: cache precondition failed for {module}'
                      f' (exit={check.returncode}); see {args.log}', flush=True)
                return 1
        if reserve and available_kib() < reserve:
            print('refusing launch: host available memory is below the requested reserve', flush=True)
            return 1
        process = subprocess.Popen(command,
                                   stdout=log, stderr=log, start_new_session=True)
        try:
            while process.poll() is None:
                total = group_rss_kib(process.pid)
                peak = max(peak, total)
                reasons = []
                if total > args.rss_limit_gib * 1024 * 1024:
                    reasons.append('group RSS limit')
                if time.monotonic() - start > args.timeout_seconds:
                    reasons.append('wall-clock limit')
                if reserve and available_kib() < reserve:
                    reasons.append('host available-memory reserve')
                if reasons:
                    print(f'interrupt elapsed={time.monotonic()-start:.1f}s rss_kb={total}'
                          f' reason={", ".join(reasons)}', flush=True)
                    interrupt_group(process, signal.SIGINT)
                    stopped = True
                    break
                time.sleep(0.25)
            try:
                result = process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                interrupt_group(process, signal.SIGKILL)
                result = process.wait()
        except BaseException:
            interrupt_group(process, signal.SIGKILL)
            process.wait()
            raise
    print(f'exit={result} elapsed={time.monotonic()-start:.1f}s observed_group_peak_kb={peak}', flush=True)
    return 1 if stopped else result


if __name__ == '__main__':
    sys.exit(main())
