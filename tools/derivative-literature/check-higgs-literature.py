#!/usr/bin/env python3
"""Independent per-paper queue; a discrepancy never skips later papers.

Exact ordinary-derivative/free specializations only. No result is a Lean premise.
"""
from fractions import Fraction as Q
from pathlib import Path
from runpy import run_path
import json

api = run_path(str(Path(__file__).with_name('check-higgs-four.py')))
evaluate, rank = (api[n] for n in ['evaluate', 'rank'])
add, scale, multiply, coefficient = (api[n] for n in ['add', 'scale', 'multiply', 'coefficient'])
UNIT, ETA, derivative = (api[n] for n in ['UNIT', 'ETA', 'derivative'])


def cases():
    amplitudes = [tuple(tuple(int(i == j) for j in range(4)) for i in range(4)),
                  tuple((1, 1, 1, 1) for _ in range(4)),
                  ((1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 1, 1), (1, 0, 0, 1)),
                  ((1, 0, 1, 0), (0, 1, 0, 1), (1, 1, 0, 0), (0, 0, 1, 1))]
    for sine, cosine in [(1, 0), (0, 1), (0, -1), (Q(3, 5), Q(4, 5))]:
        k = ((1, 0, 0, 1), (1, 0, 0, -1),
             (-1, -sine, 0, -cosine), (-1, sine, 0, cosine))
        for v in amplitudes:
            yield k, v


def eboli_native(k, v):
    fields = [{UNIT[s]: Q(row[s]) for s in range(4) if row[s]} for row in v]
    first = [[derivative(k, i, p) for i in range(4)] for p in fields]
    inner = lambda i, j: add(*(multiply(first[2+a][i], first[a][j]) for a in range(2)))
    s0 = add(*(scale(ETA[i]*ETA[j], multiply(inner(i, j), inner(i, j)))
               for i in range(4) for j in range(4)))
    s1 = add(*(scale(ETA[i]*ETA[j], multiply(inner(i, i), inner(j, j)))
               for i in range(4) for j in range(4)))
    s2 = add(*(scale(ETA[i]*ETA[j], multiply(inner(i, j), inner(j, i)))
               for i in range(4) for j in range(4)))
    return tuple(map(coefficient, [s0, s1, s2]))


def murphy():
    rows = [evaluate(k, v)[0] for k, v in cases()]
    assert rows[::4][:3] == [(2, 8, 2), (8, 8, 0), (0, 8, 8)]
    assert rank(rows) == 3
    return dict(checks=len(rows), native_order=['q1', 'q2', 'q3'], rank=3)


def li(first_factor=4):
    rows = []
    for k, v in cases():
        q, native = evaluate(k, v)
        assert native == (first_factor*q[2], q[0], q[1]-q[0]-q[2]), \
            'Li Eq. (4.8) native-to-Murphy dictionary differs'
        rows.append(native)
    assert rank(rows) == 3
    return dict(checks=len(rows), native_map=['4*q3', 'q1', 'q2-q1-q3'], rank=3)


def eboli():
    rows = []
    for k, v in cases():
        q, _ = evaluate(k, v)
        native = eboli_native(k, v)
        assert native == (q[1], q[2], q[0])
        rows.append(native)
    assert rank(rows) == 3 and rank([r[:2] for r in rows]) == 2
    return dict(checks=len(rows), native_order=['q2', 'q3', 'q1'], rank=3,
                omitted_S2_rank=2)


def queue(li_factor=4):
    results = []
    for paper, check in [('Murphy 2005.00059v6 Table 2', murphy),
                         ('Li et al. 2005.00008v3 Eq. (4.8)', lambda: li(li_factor)),
                         ('Eboli-Gonzalez-Garcia 1604.03555v1 Eq. (16)', eboli)]:
        try:
            results.append(dict(paper=paper, status='agreement', **check()))
        except (AssertionError, ArithmeticError) as exc:
            results.append(dict(paper=paper, status='discrepancy', detail=str(exc)))
    return results


def main():
    actual = queue()
    control = queue(li_factor=3)
    assert [r['status'] for r in control] == ['agreement', 'discrepancy', 'agreement']
    print(json.dumps(dict(scope='free gaugeless H4D4; diagnostic, not a Lean premise',
                          papers=actual, continuation_control='bad Li factor detected; Eboli still checked'),
                     indent=2))
    return int(any(r['status'] != 'agreement' for r in actual))


if __name__ == '__main__':
    raise SystemExit(main())
