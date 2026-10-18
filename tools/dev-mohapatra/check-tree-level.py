#!/usr/bin/env python3
"""Exact exterior-polynomial diagnostic for the declared one-N chiral action.

Uses only Python's standard library. It is not a Lean proof premise and does
not identify the paper's suppressed coupling or charge-conjugation conventions.
"""
from fractions import Fraction
from itertools import product


def add(*polynomials):
    out = {}
    for polynomial in polynomials:
        for monomial, coefficient in polynomial.items():
            out[monomial] = out.get(monomial, 0) + coefficient
    return {m: c for m, c in out.items() if c}


def scale(c, polynomial):
    return {m: c * x for m, x in polynomial.items() if c * x}


def parity(indices):
    return (-1) ** sum(x > y for i, x in enumerate(indices) for y in indices[i + 1:])


def mul(left, right):
    out = {}
    for a, ca in left.items():
        for b, cb in right.items():
            if set(a).intersection(b):
                continue
            sequence = a + b
            monomial = tuple(sorted(sequence))
            out[monomial] = out.get(monomial, 0) + parity(sequence) * ca * cb
    return {m: c for m, c in out.items() if c}


def field(species, color, spin):
    return {(species * 6 + color * 2 + spin,): Fraction(1)}


def pair(x, y):
    return add(mul(x[0], y[1]), scale(-1, mul(x[1], y[0])))


def eps(a, b, c):
    return parity((a, b, c)) if len({a, b, c}) == 3 else 0


u = [[field(0, a, r) for r in range(2)] for a in range(3)]
d = [[field(1, a, r) for r in range(2)] for a in range(3)]
s = [[field(2, a, r) for r in range(2)] for a in range(3)]
down = [add(*(scale(eps(a, b, c), pair(d[b], s[c]))
              for b, c in product(range(3), repeat=2))) for a in range(3)]
current = [add(*(mul(u[a][r], down[a]) for a in range(3))) for r in range(2)]
current_product = mul(current[0], current[1])
printed = add(*(mul(pair(u[a], u[b]), mul(down[a], down[b]))
                for a, b in product(range(3), repeat=2)))
assert mul(current[1], current[0]) == scale(-1, current_product)
assert printed == scale(2, current_product)
assert current_product

# This order is the prior sourceExterior probe, not sorted component order.
probe_order = (0, 10, 5, 14, 7, 15)
evaluation = parity(probe_order) * current_product.get(tuple(sorted(probe_order)), 0)
assert evaluation == 1

for chi_mass_sq, majorana_mass, lam, lam_ds in [(2, 3, 1, 1), (5, 7, 2, -3)]:
    m, mass, a, b = map(Fraction, (chi_mass_sq, majorana_mass, lam, lam_ds))
    g = a * b / m
    n = [scale(-g / mass, j) for j in current]
    vertices = [pair(n, u[color]) for color in range(3)]
    chi = [scale(-a / m, j) for j in vertices]
    chi_bar = [scale(-b / m, j) for j in down]
    scalar_terms = [add(scale(m, mul(chi[c], chi_bar[c])),
                        scale(a, mul(vertices[c], chi_bar[c])),
                        scale(b, mul(chi[c], down[c]))) for c in range(3)]
    on_shell = add(scale(-mass, mul(n[0], n[1])), *scalar_terms)
    assert on_shell == scale(g * g / mass, current_product)
    assert on_shell == scale((a * b) ** 2 / (2 * m * m * mass), printed)

print(f"Exact tree diagnostic passed: {len(current_product)} nonzero degree-six monomials; "
      "probe current-product = 1, printed contraction = 2; two rational UV substitutions.")
