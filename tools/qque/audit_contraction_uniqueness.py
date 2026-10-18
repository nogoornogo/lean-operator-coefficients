"""Exact finite-generator contraction audit; not a replacement for Lean.

Check invariant epsilon vectors and complex nullity one for the explicit
SU(2), SU(3), and SL(2,C) elements used in the uniqueness proofs. Gaussian
rationals are pairs of Fractions; elimination is over the rational real block.
No numerical tolerance, random sampling, or external dependency is used.
"""

from fractions import Fraction as F
from itertools import product
from functools import reduce
import unittest

from audit_one_generation import parity


def z(real=0, imag=0):
    return F(real), F(imag)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def conjugate(matrix):
    return [[(r, -i) for r, i in row] for row in matrix]


def tensor(matrices):
    indices = list(product(*(range(len(m)) for m in matrices)))
    return [[reduce(mul, (m[r][c] for m, r, c in zip(matrices, row, col)), z(1))
             for col in indices] for row in indices]


def epsilon(indices):
    return parity(indices) if len(set(indices)) == len(indices) else 0


def rank(rows):
    rows = [list(row) for row in rows]
    pivot = 0
    for col in range(len(rows[0])):
        found = next((r for r in range(pivot, len(rows)) if rows[r][col]), None)
        if found is None:
            continue
        rows[pivot], rows[found] = rows[found], rows[pivot]
        scale = rows[pivot][col]
        rows[pivot] = [v / scale for v in rows[pivot]]
        for r in range(pivot + 1, len(rows)):
            scale = rows[r][col]
            if scale:
                rows[r] = [v - scale * w for v, w in zip(rows[r], rows[pivot])]
        pivot += 1
    return pivot


class ContractionUniqueness(unittest.TestCase):
    def check_unique(self, actions, coefficient):
        size = len(coefficient)
        self.assertTrue(any(coefficient))
        constraints = []
        for action in actions:
            for col in range(size):
                value = reduce(add, (mul(z(coefficient[r]), action[r][col])
                                     for r in range(size)), z())
                self.assertEqual(value, z(coefficient[col]))
                equation = [add(action[r][col], z(-int(r == col))) for r in range(size)]
                constraints.append([v[0] for v in equation] + [-v[1] for v in equation])
                constraints.append([v[1] for v in equation] + [v[0] for v in equation])
        self.assertEqual(rank(constraints), 2 * (size - 1))

    def test_weak(self):
        phase = [[z(0, 1), z()], [z(), z(0, -1)]]
        flip = [[z(), z(1)], [z(-1), z()]]
        self.check_unique([tensor([g, g]) for g in [phase, flip]],
                          [epsilon(i) for i in product(range(2), repeat=2)])

    def test_color(self):
        signs = [[[z((1 if r == n else -1) if r == c else 0)
                   for c in range(3)] for r in range(3)] for n in range(3)]
        swaps = []
        for a, b in [(0, 1), (1, 2), (0, 2)]:
            p = list(range(3))
            p[a], p[b] = p[b], p[a]
            swaps.append([[z(-int(p[r] == c)) for c in range(3)] for r in range(3)])
        self.check_unique([tensor([g, g, g]) for g in signs + swaps],
                          [epsilon(i) for i in product(range(3), repeat=3)])

    def test_spinor(self):
        diagonal = [[z(1, 1), z()], [z(), z(F(1, 2), F(-1, 2))]]
        shear = [[z(1), z(1)], [z(), z(1)]]
        self.check_unique([tensor([g, g, conjugate(g), conjugate(g)])
                           for g in [diagonal, shear]],
                          [epsilon(i[:2]) * epsilon(i[2:])
                           for i in product(range(2), repeat=4)])


if __name__ == "__main__":
    unittest.main()
