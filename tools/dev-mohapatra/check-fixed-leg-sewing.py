#!/usr/bin/env python3
"""Fixed external legs from finite vertex/propagator contraction lists.

Independent of polynomial elimination and its Python implementation.
Zero-momentum mass inverse and quadratic half are supplied tree conventions.
This does not certify an S-matrix or the paper's convention adoption.
"""
from fractions import Fraction
from itertools import product, permutations

# species, color, spin; determinant probe order from the Lean coefficient map.
legs = ((0, 0, 0), (1, 2, 0), (0, 2, 1),
        (2, 1, 0), (1, 0, 1), (2, 1, 1))

def parity(xs):
    return (-1) ** sum(x > y for i, x in enumerate(xs) for y in xs[i + 1:])
def eps3(a, b, c):
    return parity((a, b, c)) if len({a, b, c}) == 3 else 0
def eps2(a, b):
    return (b - a) if a != b else 0

def probe_sign(sequence):
    if len(set(sequence)) != 6 or set(sequence) != set(legs):
        return 0
    return parity(tuple(legs.index(x) for x in sequence))

# Independently enumerate source vertex legs in u,d,s order.
sources = [[], []]
for r, a, b, c, j, k in product(range(2), range(3), range(3), range(3), range(2), range(2)):
    weight = (-1 if r == 0 else 1) * eps3(a, b, c) * eps2(j, k)
    if weight:
        sources[r].append((weight, ((0, a, 1-r), (1, b, j), (2, c, k))))

# Independently assign the two external legs of each species to literal uu/ds/ds slots.
by_species = [[x for x in legs if x[0] == species] for species in range(3)]
operator_probe = 0
for ups, downs, strange in product(*(list(permutations(xs)) for xs in by_species)):
    sequence = (ups[0], ups[1], downs[0], strange[0], downs[1], strange[1])
    color = eps3(ups[0][1], downs[0][1], strange[0][1]) * eps3(ups[1][1], downs[1][1], strange[1][1])
    spin = eps2(ups[0][2], ups[1][2]) * eps2(downs[0][2], strange[0][2]) * eps2(downs[1][2], strange[1][2])
    operator_probe += color * spin * probe_sign(sequence)
assert operator_probe == 2

cases = 0
for m0, mass0, a0, z0 in ((2, 3, 1, 1), (5, 7, 2, -3)):
    for scalar_sign, flavor_weight in product((1, -1), (1, 2)):
        m, mass, a, b = map(Fraction, (scalar_sign*m0, mass0, a0, flavor_weight*z0))
        inverse = ((0, 1/mass), (-1/mass, 0))
        g = a*b/m
        result = Fraction(0)
        for r, t in product(range(2), repeat=2):
            for wl, left in sources[r]:
                for wr, right in sources[t]:
                    result += Fraction(1, 2) * inverse[r][t] * g*g * wl*wr * probe_sign(left+right)
        assert result == g*g/mass
        # Inverse-C target has three minus signs; the two source signs cancel.
        assert result / (-operator_probe) == -(a*b)**2/(2*m*m*mass)
        cases += 1
print(f'Fixed-leg sewing passed: independent literal probe = {operator_probe}; '
      f'{cases} exact vertex/mass-inverse cases; no polynomial elimination imported.')
