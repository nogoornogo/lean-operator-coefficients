#!/usr/bin/env python3
"""Exact external regression; no result is a Lean premise or rank certificate.

Coordinates: color z0,z1, weak, left spin, right spin, integral 6Y.
The inverse character is used in positive-root constant-term extraction.
Source conventions and limitations are documented in README.md.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from math import comb
from pathlib import Path
import csv
import json

ZERO = (0,) * 6
ROOTS = ((1, -1, 0, 0, 0, 0), (1, 2, 0, 0, 0, 0),
         (2, 1, 0, 0, 0, 0), (0, 0, 2, 0, 0, 0),
         (0, 0, 0, 2, 0, 0), (0, 0, 0, 0, 2, 0))
HYPER = (1, 4, -2, -3, -6, -1, -4, 2, 3, 6)
RIGHT = (False, True, True, False, True, True, False, False, True, False)
DIMENSIONS = (36, 18, 18, 12, 6, 36, 18, 18, 12, 6)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def scale(n, w):
    return tuple(n * x for x in w)


def slots(s):
    """Gauge dual negates gauge weights; signed conjugation swaps spin factor."""
    base = s % 5
    colors = ((1, 0), (0, 1), (-1, -1)) if base < 3 else ((0, 0),)
    weak = (-1, 1) if base in (0, 3) else (0,)
    sign = -1 if s >= 5 else 1
    return [(*scale(sign, c), sign * w, 0 if RIGHT[s] else spin,
             spin if RIGHT[s] else 0, HYPER[s])
            for c, w, spin, _ in product(colors, weak, (-1, 1), range(3))]


@lru_cache(maxsize=None)
def exterior_table(s):
    """Grouped DP for product (1+t*x^weight)^multiplicity; spatial weights only.

    Hypercharge is homogeneous n*HYPER[s]. Upper degrees use complement
    subsets; the sum of all spatial slot weights is zero.
    """
    weights = Counter(w[:5] for w in slots(s))
    top = DIMENSIONS[s] // 2
    result = [Counter() for _ in range(top + 1)]
    result[0][(0,) * 5] = 1
    used = 0
    for w, copies in weights.items():
        nxt = [Counter() for _ in range(top + 1)]
        for n in range(min(used, top) + 1):
            for k in range(min(copies, top - n) + 1):
                shift, factor = scale(k, w), comb(copies, k)
                for v, count in result[n].items():
                    nxt[n + k][add(v, shift)] += factor * count
        result, used = nxt, used + copies
    for n, poly in enumerate(result):
        assert sum(poly.values()) == comb(DIMENSIONS[s], n), (s, n)
    return result


def coefficient(s, n, w):
    if not 0 <= n <= DIMENSIONS[s] or w[5] != n * HYPER[s]:
        return 0
    if n > DIMENSIONS[s] // 2:
        return exterior_table(s)[DIMENSIONS[s] - n].get(scale(-1, w[:5]), 0)
    return exterior_table(s)[n].get(w[:5], 0)


def extract(coeff, m, delta):
    total = 0
    for mask in range(1 << len(ROOTS)):
        root = ZERO
        for i, r in enumerate(ROOTS):
            if mask & (1 << i):
                root = add(root, r)
        for j in range(m + 1):
            boson = (0, 0, m - 2 * j, 0, 0, 3 * delta)
            total += (-1) ** mask.bit_count() * coeff(scale(-1, add(root, boson)))
    return total


def multiplicity(s, n, m, delta):
    return extract(lambda w: coefficient(s, n, w), m, delta)


def brute(s, n):
    poly = Counter()
    for selected in combinations(slots(s), n):
        w = ZERO
        for v in selected:
            w = add(w, v)
        poly[w] += 1
    return poly


def tensor_slots(species):
    result = Counter({ZERO: 1})
    for s in species:
        nxt = Counter()
        for u, a in result.items():
            for v, b in Counter(slots(s)).items():
                nxt[add(u, v)] += a * b
        result = nxt
    return result


def self_checks():
    assert extract(lambda w: int(w == ZERO), 0, 0) == 1
    for s in range(10):
        ws = slots(s)
        assert len(ws) == DIMENSIONS[s]
        assert tuple(sum(w[i] for w in ws) for i in range(5)) == (0,) * 5
        assert Counter(ws) == Counter((w[1], w[0], *w[2:]) for w in ws)
        assert Counter(ws) == Counter((-w[0], w[1] - w[0], *w[2:]) for w in ws)
        for coord in (2, 3, 4):
            reflected = [tuple(-x if i == coord else x for i, x in enumerate(w)) for w in ws]
            assert Counter(ws) == Counter(reflected)
        for n in (0, 1, 2, DIMENSIONS[s] - 1, DIMENSIONS[s]):
            direct = brute(s, n)
            assert sum(direct.values()) == comb(DIMENSIONS[s], n)
            assert all(coefficient(s, n, w) == count for w, count in direct.items())
        for n in (0, 2):
            direct = brute(s, n)
            for m in range(5):
                for delta in range(-m, m + 1, 2):
                    assert multiplicity(s, n, m, delta) == extract(lambda w: direct.get(w, 0), m, delta)
    for s in range(5):
        conjugated = [(-w[0], -w[1], -w[2], w[4], w[3], -w[5]) for w in slots(s)]
        assert Counter(conjugated) == Counter(slots(s + 5))
    assert multiplicity(3, 2, 2, 2) == 6
    assert multiplicity(8, 2, 2, -2) == 6
    assert all(multiplicity(0, 24, m, -8) == 0 for m in range(14, 25, 2))
    # Distinct DUQL slots: determinant, weak epsilon, two spin epsilons,
    # and independent three-dimensional flavor carriers: 3^4 coefficients.
    duql = tensor_slots((2, 1, 0, 3))
    assert sum(duql.values()) == 18 * 18 * 36 * 12
    assert extract(lambda w: duql.get(w, 0), 0, 0) == 81
    # A conjugate pair has one left and one right spinor, hence no scalar.
    pair = tensor_slots((0, 5))
    assert extract(lambda w: pair.get(w, 0), 0, 0) == 0


def main():
    self_checks()
    path = Path(__file__).with_name('constant-content-ranks.csv')
    known = unknown_positive = unknown_zero = 0
    species_seen = set()
    neutral_values = {}
    with path.open(newline='') as inp:
        for row in csv.DictReader(inp):
            s, n, m, delta, columns = (int(row[k]) for k in ('species', 'fermions', 'm', 'delta', 'columns'))
            assert columns == comb(DIMENSIONS[s], n) * (m + 1)
            value = multiplicity(s, n, m, delta)
            assert 0 <= value <= columns, (s, n, m, delta, value)
            species_seen.add(s)
            if row['rank']:
                assert columns - value == int(row['rank']), (row, value)
                known += 1
            else:
                assert row['status'] == 'unclassified'
                assert n % 2 == 0 and n * HYPER[s] + 3 * delta == 0
                unknown_positive += value > 0
                unknown_zero += value == 0
                neutral_values[s, n, m, delta] = (columns, value, columns - value)
    assert species_seen == set(range(10))
    assert (known, unknown_positive, unknown_zero) == (19161, 41, 66)
    seen = set()
    with path.with_name('neutral-sparse-results.csv').open(newline='') as inp:
        for row in csv.DictReader(inp):
            key = tuple(int(row[k]) for k in ('species', 'fermions', 'm', 'delta'))
            assert key not in seen, key
            seen.add(key)
            assert tuple(int(row[k]) for k in ('columns', 'multiplicity', 'rank')) == neutral_values[key], row
    assert seen == set(neutral_values)
    print(json.dumps({'scope': 'external exact regression; not a Lean proof or classification',
                      'signed_species': 10, 'certified_rows_matched': known,
                      'sparse_neutral_rows_matched': len(seen),
                      'unclassified_diagnostic_positive': unknown_positive,
                      'unclassified_diagnostic_zero': unknown_zero}, indent=2))


if __name__ == '__main__':
    main()
