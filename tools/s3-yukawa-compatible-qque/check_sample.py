#!/usr/bin/env python3
"""Exact finite supplement to S3YukawaCompatibleQque; standard library only.

Exhaustive tensor-basis checks extend by multilinearity. This script is not
an input to Lean and does not certify physical Yukawa matching or UV physics.
"""
from itertools import permutations, product

PERMS = tuple(permutations(range(3)))
BASIS = tuple(tuple(int(i == j) for i in range(3)) for j in range(3))


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))


def permutation(p, x):
    return tuple(x[p.index(i)] for i in range(3))


def coefficient(x, y, z, r):
    # Columns (ones, coordinatewise x*y, z), matching coefficient_apply.
    a = tuple(x[i] * y[i] for i in range(3))
    return (a[1]*z[2] - a[2]*z[1] - a[0]*z[2] + a[2]*z[0]
            + a[0]*z[1] - a[1]*z[0]) * sum(r)


def main():
    for p in PERMS:
        for x, y, z, r in product(BASIS, repeat=4):
            assert coefficient(permutation(p, x), permutation(p, y),
                               permutation(p, z), tuple(sign(p)*v for v in r)) == coefficient(x, y, z, r)
    for x, y, z, r in product(BASIS, repeat=4):
        assert coefficient(y, x, z, r) == coefficient(x, y, z, r)
    assert coefficient(BASIS[0], BASIS[0], BASIS[1], BASIS[0]) == 1
    # Regression control: removing the electron sign spoils invariance.
    p = (1, 0, 2)
    x, y, z, r = BASIS[0], BASIS[0], BASIS[1], BASIS[0]
    assert coefficient(permutation(p, x), permutation(p, y), permutation(p, z), r) == -1
    print('PASS: 486 invariant basis checks; 81 symmetric basis checks; witness=1; missing-sign control=-1')


if __name__ == '__main__':
    main()
