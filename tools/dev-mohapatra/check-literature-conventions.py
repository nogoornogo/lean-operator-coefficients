#!/usr/bin/env python3
"""Literature matrices and exact 18-generator on-shell diagnostic.

Canonical normalization and transfer to the target remain adopted inputs.
No rates or loop calculations; this script is not a Lean proof premise.
"""
from fractions import Fraction
from itertools import product
from pathlib import Path
import runpy

p = runpy.run_path(str(Path(__file__).with_name('check-tree-level.py')))
add, scale, mul, eps = (p[n] for n in ('add', 'scale', 'mul', 'eps'))
u, d, s = (p[n] for n in ('u', 'd', 's'))
sigma2 = [[0, -1j], [1j, 0]]
identity = [[1, 0], [0, 1]]

def blocks(a, b, c, d):
    return [a[i] + b[i] for i in range(2)] + [c[i] + d[i] for i in range(2)]

zero = [[0, 0], [0, 0]]
def sm(c, a):
    return [[c * x for x in row] for row in a]
def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]

g0 = blocks(zero, identity, identity, zero)
g2_dev = blocks(zero, sigma2, sm(-1, sigma2), zero)
g2_old = blocks(zero, sm(-1j, sigma2), sm(1j, sigma2), zero)
c_dev = sm(1j, mm(g0, g2_dev))
c_old = mm(g2_old, g0)
assert c_dev == c_old
cinv = sm(-1, c_dev)
assert mm(c_dev, cinv) == [[int(i == j) for j in range(4)] for i in range(4)]

def literature_pair(x, y):
    # Lower right-chiral block; coefficients are exactly real integers here.
    terms = []
    for i, j in product(range(2), repeat=2):
        z = complex(cinv[i + 2][j + 2])
        assert z.imag == 0 and z.real == int(z.real)
        terms.append(scale(Fraction(int(z.real)), mul(x[i], y[j])))
    return add(*terms)

down = [add(*(scale(eps(a, b, c), literature_pair(d[b], s[c]))
              for b, c in product(range(3), repeat=2))) for a in range(3)]
target = add(*(mul(literature_pair(u[a], u[b]), mul(down[a], down[b]))
               for a, b in product(range(3), repeat=2)))
assert target == scale(-1, p['printed'])
count = 0
for scalar_sign, flavor_weight in product((1, -1), (1, 2)):
    m, mass, lam, z = map(Fraction, (scalar_sign * 2, 3, 1, 1))
    b = flavor_weight * z
    # Source +M/2 inverse-C mass is -M n0 n1.
    # Both source vertices use literature_pair, so both local couplings flip.
    a_local, b_local = -lam, -b
    g = a_local * b_local / m
    n = [scale(-g / mass, j) for j in p['current']]
    vertices = [literature_pair(n, u[a]) for a in range(3)]
    chi = [scale(-lam / m, j) for j in vertices]
    chi_bar = [scale(-b / m, j) for j in down]
    scalar_terms = [add(scale(m, mul(chi[a], chi_bar[a])),
                        scale(lam, mul(vertices[a], chi_bar[a])),
                        scale(b, mul(chi[a], down[a]))) for a in range(3)]
    action = add(scale(mass / 2, literature_pair(n, n)), *scalar_terms)
    coefficient = -(lam * b) ** 2 / (2 * m * m * mass)
    assert action == scale(coefficient, target)
    assert coefficient == -(flavor_weight ** 2) * Fraction(1, 24)
    count += 1
print(f'Literature diagnostic passed: two independently specified C matrices; '
      f'{len(target)} target monomials; {count} signed-mass/flavor on-shell cases.')
