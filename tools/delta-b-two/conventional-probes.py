"""Exact conventional all-right contraction regression, not a Lean proof.

Uses 48 species permutations and all 225 degree-(2,4) monomials in a
12-generator Grassmann space (six quark components per species). No floating
point, external packages, physical matching or numerical simulation.
"""
from fractions import Fraction
from itertools import combinations, permutations


def eps(xs):
    if len(set(xs)) != len(xs):
        return 0
    return (-1) ** sum(a > b for i, a in enumerate(xs) for b in xs[i + 1:])


def sss(c):
    i, j, k, l, m, n = c
    return (eps((i, k, m)) * eps((j, l, n))
            + eps((j, k, m)) * eps((i, l, n))
            + eps((i, l, m)) * eps((j, k, n))
            + eps((j, l, m)) * eps((i, k, n)))


def aas(c):
    i, j, k, l, m, n = c
    return eps((i, j, m)) * eps((k, l, n)) + eps((i, j, n)) * eps((k, l, m))


def ordered(family, slots):
    sign = 1
    if family == 1:
        slots = tuple(slots[i] for i in (0, 2, 1, 3, 4, 5))
        sign = -1  # (u,d,u,d,d,d) -> (u,u,d,d,d,d)
    colors, spins = zip(*slots)
    color = aas(colors) if family == 3 else sss(colors)
    return sign * color * eps(spins[:2]) * eps(spins[2:4]) * eps(spins[4:])


SPECIES_PERMS = tuple(
    (u[0], d[0], u[1], d[1], d[2], d[3])
    for u in permutations((0, 2)) for d in permutations((1, 3, 4, 5)))
assert len(set(SPECIES_PERMS)) == 48


def alternating(family, slots):
    return sum(eps(p) * ordered(family, tuple(slots[i] for i in p))
               for p in SPECIES_PERMS)


def main():
    colors = (0, 0, 1, 1, 2, 2)
    probes = [tuple(zip(colors, spins))
              for spins in ((0, 1, 0, 1, 0, 1), (0, 0, 1, 1, 0, 1))]
    values = {k: tuple(alternating(k, p) for p in probes) for k in (1, 2, 3)}
    assert values == {1: (0, 48), 2: (48, -12), 3: (16, -20)}
    determinant = values[3][0] * values[2][1] - values[2][0] * values[3][1]
    assert determinant == 768  # Columns O3, O2: no 1/48 normalization.
    components = tuple((c, s) for c in range(3) for s in range(2))
    for up in combinations(components, 2):
        for down in combinations(components, 4):
            slots = (up[0], down[0], up[1], down[1], down[2], down[3])
            t = tuple(alternating(k, slots) for k in (1, 2, 3))
            assert t[1] - t[0] == 3 * t[2]
    for probe, target in enumerate(((1, 0), (0, 1))):
        alpha = -Fraction(target[0], 64) - Fraction(target[1], 16)
        beta = Fraction(5 * target[0], 192) + Fraction(target[1], 48)
        assert tuple(alpha * values[3][i] + beta * values[2][i]
                     for i in range(2)) == target
    q1 = tuple(-4 * x for x in values[3])
    q4 = tuple(-Fraction(4, 5) * values[1][i] - Fraction(16, 5) * values[2][i]
               for i in range(2))
    assert q1 == (-64, 80) and q4 == (-Fraction(768, 5), 0)
    print('O1/O2/O3 probes:', values)
    print('O3/O2 determinant: 768; inverse regression passed')
    print('Fierz regression: all 225 Grassmann basis monomials passed')
    print('Q1/Q4 convention probes:', q1, q4)


if __name__ == '__main__':
    main()
