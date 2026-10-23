#!/usr/bin/env python3
"""Exact colored-wave and literature-density diagnostic; not a Lean premise.

Reuses only sparse polynomial arithmetic from the independent scalar check,
not its rank, invariant coordinates or expected paper values. Standard library.
"""
from fractions import Fraction as Q
from functools import reduce
from itertools import permutations
from pathlib import Path
from runpy import run_path
import json

poly = run_path(str(Path(__file__).with_name('check-scalar-waves.py')))
add, scale, multiply = (poly[n] for n in ['add', 'scale', 'multiply'])
coefficient, compositions = (poly[n] for n in ['coefficient', 'compositions'])
UNIT, ETA, ZERO = (poly[n] for n in ['UNIT', 'ETA', 'ZERO'])


def derivative(k, i, p):
    return {a: c*sum(a[s]*k[s][i] for s in range(4)) for a, c in p.items()
            if c*sum(a[s]*k[s][i] for s in range(4))}


def evaluate(k, v):
    fields = [{UNIT[s]: Q(v[j][s]) for s in range(4) if v[j][s]} for j in range(4)]
    d = lambda i, p: derivative(k, i, p)
    box = lambda p: add(*(scale(ETA[i], d(i, d(i, p))) for i in range(4)))
    first = [[d(i, p) for i in range(4)] for p in fields]
    m = [[add(*(multiply(first[2+a][i], first[a][j]) for a in range(2)))
          for j in range(4)] for i in range(4)]
    q1 = add(*(scale(ETA[i]*ETA[j], multiply(m[i][j], m[j][i]))
               for i in range(4) for j in range(4)))
    q2 = add(*(scale(ETA[i]*ETA[j], multiply(m[i][j], m[i][j]))
               for i in range(4) for j in range(4)))
    q3 = multiply(add(*(scale(ETA[i], m[i][i]) for i in range(4))),
                  add(*(scale(ETA[i], m[i][i]) for i in range(4))))
    rho = add(*(multiply(fields[2+a], fields[a]) for a in range(2)))
    current = [add(*(multiply(fields[2+a], first[a][i]) for a in range(2))) for i in range(4)]
    conjugate = [add(*(multiply(first[2+a][i], fields[a]) for a in range(2))) for i in range(4)]
    li1 = multiply(rho, box(box(rho)))
    li2 = add(*(scale(ETA[i]*ETA[j], multiply(
        add(*(multiply(fields[2+a], d(i, first[a][j])) for a in range(2))),
        add(*(multiply(d(i, first[2+a][j]), fields[a]) for a in range(2)))))
                for i in range(4) for j in range(4)))
    li3 = add(*(scale(ETA[i], multiply(conjugate[i], box(current[i]))) for i in range(4)))
    return tuple(map(coefficient, [q1, q2, q3])), tuple(map(coefficient, [li1, li2, li3]))


def rank(rows):
    a = [list(map(Q, row)) for row in rows]
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        a[r] = [x/a[r][c] for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][c]
                a[i] = [x-z*y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def value(k, a):
    return reduce(
        lambda x, y: x*y, (k[s][i]**a[4*s+i] for s in range(4) for i in range(4)), Q(1))


def main():
    identity = tuple(tuple(int(i == j) for j in range(4)) for i in range(4))
    amplitudes = [identity, tuple(tuple(1 for _ in range(4)) for _ in range(4)),
                  ((1, 1, 0, 0), (0, 1, 1, 0), (0, 0, 1, 1), (1, 0, 0, 1)),
                  ((1, 0, 1, 0), (0, 1, 0, 1), (1, 1, 0, 0), (0, 0, 1, 1))]
    configurations = []
    relations = 0
    comparisons = 0
    for sine, cosine in [(1, 0), (0, 1), (0, -1), (Q(3, 5), Q(4, 5))]:
        k = ((1, 0, 0, 1), (1, 0, 0, -1), (-1, -sine, 0, -cosine), (-1, sine, 0, cosine))
        assert all(sum(p[i] for p in k) == 0 for i in range(4))
        assert all(sum(ETA[i]*p[i]**2 for i in range(4)) == 0 for p in k)
        for d in range(4):
            for a in compositions(d, 16):
                for i in range(4):
                    total = Q(0)
                    for s in range(4):
                        b = list(a)
                        b[4*s+i] += 1
                        total += value(k, b)
                    assert total == 0
                    relations += 1
        for v in amplitudes:
            q, li = evaluate(k, v)
            assert li == (4*q[2], q[0], q[1]-q[0]-q[2])
            transformed = (tuple(x+y for x, y in zip(v[0], v[1])), v[1],
                           v[2], tuple(y-x for x, y in zip(v[2], v[3])))
            assert evaluate(k, transformed) == (q, li)
            comparisons += 1
            for permutation in permutations(range(4)):
                kp = tuple(k[s] for s in permutation)
                vp = tuple(tuple(row[s] for s in permutation) for row in v)
                assert evaluate(kp, vp) == (q, li)
        configurations.append(tuple(str(x) for x in evaluate(k, identity)[0]))
    gram = configurations[:3]
    assert gram == [('2', '8', '2'), ('8', '8', '0'), ('0', '8', '8')]
    assert rank(gram) == 3 and rank([r[:2] for r in gram]) == 2
    k = ((1, 0, 0, 1), (1, 0, 0, -1), (-1, -1, 0, 0), (-1, 1, 0, 0))
    nonconserving = tuple(tuple(-x for x in p) if s == 0 else p for s, p in enumerate(k))
    field_product = multiply(*({UNIT[s]: Q(1)} for s in range(4)))
    assert coefficient(derivative(nonconserving, 0, field_product)) == -2
    nonnull = ((2, 0, 0, 1), (0, 0, 0, -1), k[2], k[3])
    assert all(sum(p[i] for p in nonnull) == 0 for i in range(4))
    wave = add(*(scale(ETA[i], derivative(nonnull, i, derivative(nonnull, i,
                   {UNIT[0]: Q(1)}))) for i in range(4)))
    assert coefficient(multiply(wave, *({UNIT[s]: Q(1)} for s in range(1, 4)))) == 3
    print(json.dumps(dict(role='exact diagnostic, not a Lean premise',
        gram=gram, rank=3, divergence_checks=relations,
        literal_Li_density_checks=comparisons, simultaneous_wave_permutations=24*comparisons,
        Li_native_map=['4*q3', 'q1', 'q2-q1-q3'],
        Eboli_native_order=['q2', 'q3', 'q1'],
        negative_controls=dict(nonconserving_divergence=-2, nonnull_eom_product=3,
                               omitted_candidate_rank=2)), indent=2))


if __name__ == '__main__':
    main()
