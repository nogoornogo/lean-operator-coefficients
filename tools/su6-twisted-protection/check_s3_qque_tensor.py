#!/usr/bin/env python3
"""Exact signed-orbit counts for the two three-generation S3 qque controls.

Python standard library only. No UV model or arbitrary group classification.
Orbit counts supplement the Lean zero/nonzero certificates; they are not
imported as proof premises. Run from repository root with python3.
"""
from itertools import permutations, product
import unittest

GROUP = tuple(permutations(range(3)))


def sign(g):
    return (-1) ** sum(g[i] > g[j] for i in range(3) for j in range(i + 1, 3))


def invariant_orbits(nodes, transform, twist):
    remaining = set(nodes)
    count = 0
    while remaining:
        seed = min(remaining)
        weights = {seed: 1}
        pending = [seed]
        consistent = True
        while pending:
            x = pending.pop()
            for g in GROUP:
                y = transform(g, x)
                weight = weights[x] * sign(g) ** twist
                if y in weights:
                    consistent &= weights[y] == weight
                else:
                    weights[y] = weight
                    pending.append(y)
        remaining.difference_update(weights)
        count += int(consistent)
    return count


def qque_dimension(symmetric, twist):
    nodes = tuple((i, j) for i, j in product(range(3), repeat=2)
                  if not symmetric or i <= j)

    def transform(g, x):
        image = (g[x[0]], g[x[1]])
        return tuple(sorted(image)) if symmetric else image

    # Each of the three u and three e copy indices is fixed, giving 9 copies.
    return 9 * invariant_orbits(nodes, transform, twist)


class TensorChecks(unittest.TestCase):
    def test_single_sign_with_statistics(self):
        self.assertEqual(qque_dimension(False, 1), 9)
        self.assertEqual(qque_dimension(True, 1), 0)

    def test_two_sign_factors(self):
        self.assertEqual(qque_dimension(False, 2), 18)
        self.assertEqual(qque_dimension(True, 2), 18)

    def test_no_common_single_factor(self):
        count = invariant_orbits(range(3), lambda g, i: g[i], 1)
        self.assertEqual(count, 0)


if __name__ == "__main__":
    print("S3 qque: single sign ordered/symmetric = 9/0; double sign = 18/18.")
    unittest.main()
