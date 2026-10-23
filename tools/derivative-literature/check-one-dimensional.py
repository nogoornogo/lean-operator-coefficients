#!/usr/bin/env python3
"""Independent exact C1 diagnostic, not a Lean completeness premise.

Enumerate every commutative jet monomial at a fixed species multiplicity
and derivative degree. EOM kills monomials containing a second/higher jet;
IBP columns are actual Leibniz derivatives of the preceding degree.
"""
from fractions import Fraction
from itertools import combinations_with_replacement, product
import json


def monomials(content, degree):
    if degree < 0:
        return []
    choices = [list(combinations_with_replacement(range(degree + 1), r))
               for r in content]
    return sorted(tuple((s, k) for s, ks in enumerate(parts) for k in ks)
                  for parts in product(*choices)
                  if sum(map(sum, parts)) == degree)


def rank(rows):
    a = [[Fraction(x) for x in row] for row in rows]
    if not a:
        return 0
    pivot = 0
    for col in range(len(a[0])):
        p = next((i for i in range(pivot, len(a)) if a[i][col]), None)
        if p is None:
            continue
        a[pivot], a[p] = a[p], a[pivot]
        scale = a[pivot][col]
        a[pivot] = [x / scale for x in a[pivot]]
        for i in range(len(a)):
            if i != pivot and a[i][col]:
                scale = a[i][col]
                a[i] = [x - scale * y for x, y in zip(a[i], a[pivot])]
        pivot += 1
        if pivot == len(a):
            break
    return pivot


def sector(content, degree):
    basis = monomials(content, degree)
    index = {m: i for i, m in enumerate(basis)}
    ibp = []
    for m in monomials(content, degree - 1):
        row = [0] * len(basis)
        for j, (s, k) in enumerate(m):
            term = tuple(sorted(m[:j] + ((s, k + 1),) + m[j + 1:]))
            row[index[term]] += 1
        ibp.append(row)
    eom = []
    for i, m in enumerate(basis):
        if any(k >= 2 for _, k in m):
            eom.append([int(i == j) for j in range(len(basis))])
    # Test an explicit surviving representative, not just the predicted rank.
    # After free EOM, place all derivatives on distinct species first jets.
    representative = None
    if len(content) == 2 and degree <= min(content):
        parts = [[(s, 0)] * count for s, count in enumerate(content)]
        if degree >= 1:
            parts[0][0] = (0, 1)
        if degree == 2:
            parts[1][0] = (1, 1)
        representative = tuple(sorted(parts[0] + parts[1]))
        vector = [int(m == representative) for m in basis]
        assert rank(ibp + eom + [vector]) == rank(ibp + eom) + 1
        assert rank(ibp + eom + [vector]) == len(basis)
    return dict(content=content, degree=degree, source=len(basis),
                representative=representative,
                representative_completes_quotient=representative is not None,
                ibp_rank=rank(ibp), combined_rank=rank(ibp + eom),
                off_dimension=len(basis) - rank(ibp),
                on_dimension=len(basis) - rank(ibp + eom))


def main():
    cases = [((2,), 2, 0)] + [(content, degree, int(degree <= min(content)))
             for content in [(1, 1), (2, 2)] for degree in range(3)]
    results = []
    for content, degree, expected in cases:
        result = sector(content, degree)
        assert result['on_dimension'] == expected, result
        if content == (2,):
            assert result['off_dimension'] == 1, result
        results.append(result)
    print(json.dumps(dict(role='exact diagnostic; no Lean semantic bridge assumed',
                         sectors=results), indent=2))


if __name__ == '__main__':
    main()
