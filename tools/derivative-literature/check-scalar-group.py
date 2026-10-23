#!/usr/bin/env python3
"""Exact C2 finite-group diagnostic, supplementary to Lean proofs.

Rows use the two sign flips and the real/imaginary unit shears whose actual
SL(2,C) direction matrices are proved in LorentzFiniteControls. Polynomial
expansion, exhaustive finite coverage, and row elimination here are Python
diagnostics, not imported Lean premises or a full-group invariant dual.
Only the Python standard library is required.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import importlib.util
import json
import sys

sys.dont_write_bytecode = True

_spec = importlib.util.spec_from_file_location(
    'scalar_lorentz', Path(__file__).with_name('check-scalar-lorentz.py'))
old = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(old)

MATRICES = {
    'flipZ': [[1, 0, 0, 0], [0, -1, 0, 0], [0, 0, -1, 0], [0, 0, 0, 1]],
    'flipX': [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -1, 0], [0, 0, 0, -1]],
    'realShear': [[Q(3, 2), -1, 0, Q(-1, 2)], [-1, 1, 0, 1],
                  [0, 0, 1, 0], [Q(1, 2), -1, 0, Q(1, 2)]],
    'imagShear': [[Q(3, 2), 0, 1, Q(-1, 2)], [0, 1, 0, 0],
                  [1, 0, 1, -1], [Q(1, 2), 0, 1, Q(1, 2)]]}


def jet_transform(a, matrix):
    terms = {(0, 0, 0, 0): Q(1)}
    for i, power in enumerate(a):
        for _ in range(power):
            nxt = {}
            for b, c in terms.items():
                for j in range(4):
                    old.add(nxt, old.shift(b, j), c * matrix[i][j])
            terms = nxt
    return terms


def transform(m, matrix):
    terms = {(): Q(1)}
    for a in m:
        nxt = {}
        for tail, c in terms.items():
            for b, v in jet_transform(a, matrix).items():
                old.add(nxt, tuple(sorted(tail + (b,))), c * v)
        terms = nxt
    return terms


def equations(d, basis):
    index = {m: i for i, m in enumerate(basis)}
    rows = []

    def insert(terms):
        row = {}
        for m, c in terms:
            old.add(row, index[tuple(sorted(m))], c)
        rows.append(row)

    for m in old.monomials(4, d - 1):
        for i in range(4):
            insert((m[:j] + (old.shift(a, i),) + m[j+1:], 1)
                   for j, a in enumerate(m))
    for k in range(d - 1):
        for a in old.indices(k):
            for m in old.monomials(3, d-k-2):
                insert((m + (old.shift(a, i, 2),), 1 if i == 0 else -1)
                       for i in range(4))
    relation_rank = old.sparse_rank(rows)
    for matrix in MATRICES.values():
        for m in basis:
            terms = transform(m, matrix)
            old.add(terms, m, -1)
            insert(terms.items())
    return index, rows, relation_rank


def kernel(rows, size):
    pivots = {}
    for raw in rows:
        row = {k: Q(v) for k, v in raw.items() if v}
        while row:
            p = min(row)
            if p not in pivots:
                c = row[p]
                pivots[p] = {k: v/c for k, v in row.items()}
                break
            c = row[p]
            for k, v in pivots[p].items():
                old.add(row, k, -c*v)
    free = sorted(set(range(size)) - pivots.keys())
    dual = [Q(0)] * size
    if free:
        assert len(free) == 1
        dual[free[0]] = 1
        for p in sorted(pivots, reverse=True):
            dual[p] = -sum(v*dual[k] for k, v in pivots[p].items() if k != p)
        assert all(sum(v*dual[k] for k, v in row.items()) == 0 for row in rows)
    return len(pivots), dual


def sector(d):
    basis = old.monomials(4, d)
    index, rows, relation_rank = equations(d, basis)
    rank, dual = kernel(rows, len(basis))
    witness = {}
    if d == 0:
        witness[index[((0, 0, 0, 0),)*4]] = 1
    elif d == 4:
        units = [tuple(int(i == j) for i in range(4)) for j in range(4)]
        for i, j in product(range(4), repeat=2):
            old.add(witness, index[tuple(sorted((units[i], units[i], units[j], units[j])))],
                    (1 if i == 0 else -1)*(1 if j == 0 else -1))
    if witness:
        assert old.sparse_rank(rows + [witness]) == len(basis) == rank + 1
        value = sum(c*dual[i] for i, c in witness.items())
        assert value != 0
        dual = [x/value for x in dual]
        assert sum(c*dual[i] for i, c in witness.items()) == 1
        # The representative itself is invariant under all four matrices.
        for matrix in MATRICES.values():
            transformed = {}
            for i, c in witness.items():
                for m, v in transform(basis[i], matrix).items():
                    old.add(transformed, index[m], c*v)
            assert transformed == witness
    else:
        assert rank == len(basis)
    return dict(degree=d, source=len(basis), eom_ibp_rank=relation_rank,
                finite_group_constraints_rank=rank,
                finite_group_coefficient_dimension=len(basis)-rank,
                normalized_finite_dual_nonzero_entries=sum(x != 0 for x in dual),
                representative='phi^4' if d == 0 else 'K^2' if d == 4 else None)


if __name__ == '__main__':
    result = [sector(d) for d in [0, 2, 4]]
    assert [r['finite_group_coefficient_dimension'] for r in result] == [1, 0, 1]
    print(json.dumps(dict(role='exact finite-group diagnostic; not a Lean premise',
                         transformations=list(MATRICES), sectors=result), indent=2))
