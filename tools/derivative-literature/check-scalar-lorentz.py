#!/usr/bin/env python3
"""Exact finite C2 diagnostic; the jet/Lie/group semantic bridge is unproved.

Use all scalar jet monomials at n=4 and d=0,2,4. Rows impose ordinary
Leibniz IBP, all free wave descendants/products and six infinitesimal
Lorentz transformations. This is supplementary evidence, never a Lean premise.
"""
from fractions import Fraction
from itertools import combinations_with_replacement
import json


def indices(d):
    if d < 0:
        return []
    return [(a, b, c, d-a-b-c) for a in range(d+1)
            for b in range(d-a+1) for c in range(d-a-b+1)]


def monomials(n, d):
    if d < 0:
        return []
    jets = [a for k in range(d+1) for a in indices(k)]
    # Build only degree-compatible multisets; no jet-order truncation beyond d.
    def build(left, degree, start):
        if left == 0:
            if degree == 0:
                yield ()
            return
        for i in range(start, len(jets)):
            k = sum(jets[i])
            if k <= degree:
                for tail in build(left-1, degree-k, i):
                    yield (jets[i],) + tail
    return [tuple(sorted(m)) for m in build(n, d, 0)]


def shift(a, i, k=1):
    b = list(a)
    b[i] += k
    return tuple(b)


def add(row, key, c):
    row[key] = row.get(key, 0) + c
    if row[key] == 0:
        del row[key]


def sparse_rank(rows):
    pivots = {}
    for raw in rows:
        row = {k: Fraction(v) for k, v in raw.items() if v}
        while row:
            p = min(row)
            if p not in pivots:
                c = row[p]
                pivots[p] = {k: v/c for k, v in row.items()}
                break
            c = row[p]
            for k, v in pivots[p].items():
                add(row, k, -c*v)
    return len(pivots)


def sector(d):
    basis = monomials(4, d)
    index = {m: i for i, m in enumerate(basis)}
    assert len(index) == len(basis)
    rows = []
    def insert(terms):
        row = {}
        for m, c in terms:
            add(row, index[tuple(sorted(m))], c)
        rows.append(row)
    for m in monomials(4, d-1):
        for i in range(4):
            insert((m[:j]+(shift(a, i),)+m[j+1:], 1) for j, a in enumerate(m))
    for k in range(d-1):
        for a in indices(k):
            for m in monomials(3, d-k-2):
                insert((m+(shift(a, i, 2),), 1 if i == 0 else -1)
                       for i in range(4))
    eom_ibp_rank = sparse_rank(rows)
    for i, j in combinations_with_replacement(range(4), 2):
        if i == j:
            continue
        for m in basis:
            terms = []
            for p, a in enumerate(m):
                for u, v, sign in [(i, j, 1), (j, i, 1 if i == 0 else -1)]:
                    if a[u]:
                        b = list(a)
                        b[u] -= 1
                        b[v] += 1
                        terms.append((m[:p]+(tuple(b),)+m[p+1:], a[u]*sign))
            insert(terms)
    combined_rank = sparse_rank(rows)
    # Actual polynomial coordinates of phi^4 and K^2 in this complete
    # finite monomial list. Appending their columns must close the quotient.
    witness = {}
    if d == 0:
        witness[index[((0, 0, 0, 0),) * 4]] = 1
    elif d == 4:
        units = [tuple(int(i == j) for i in range(4)) for j in range(4)]
        for i in range(4):
            for j in range(4):
                m = tuple(sorted((units[i], units[i], units[j], units[j])))
                add(witness, index[m], (1 if i == 0 else -1) *
                    (1 if j == 0 else -1))
    if witness:
        assert sparse_rank(rows + [witness]) == combined_rank + 1
        assert sparse_rank(rows + [witness]) == len(basis)
    else:
        assert combined_rank == len(basis)
    return dict(degree=d, source=len(basis), eom_ibp_rank=eom_ibp_rank,
                explicit_witness='phi^4' if d == 0 else 'K^2' if d == 4 else None,
                witness_completes_finite_quotient=bool(witness),
                all_constraints_rank=combined_rank,
                infinitesimal_coefficient_dimension=len(basis)-combined_rank)


if __name__ == '__main__':
    result = [sector(d) for d in [0, 2, 4]]
    assert [r['infinitesimal_coefficient_dimension'] for r in result] == [1, 0, 1], result
    print(json.dumps(dict(role='exact diagnostic; Lie/group and source bridge not proved',
                         sectors=result), indent=2))
