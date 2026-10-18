"""Exact two-constituent Grassmann cross-check; not a Lean proof or GUT model.

Q has two flavor components, u_R pairs with the first and e_R with the
second. The flavor coefficient is delta(p,0)delta(r,1) + its Q-slot swap.
"""

from collections import defaultdict
from itertools import combinations, permutations, product
import unittest

from audit_one_generation import parity, wedge


def q(flavor, color, weak, spin):
    return 12 * flavor + 4 * color + 2 * weak + spin


def u(color, spin):
    return 24 + 2 * color + spin


def e(spin):
    return 30 + spin


def ordered(indices):
    a, b, c, d = indices
    if not (0 <= a < 24 and 0 <= b < 24 and 24 <= c < 30 and 30 <= d < 32):
        return 0
    if a // 12 == b // 12:
        return 0
    colors = ((a % 12) // 4, (b % 12) // 4, (c - 24) // 2)
    weak = ((a // 2) % 2, (b // 2) % 2)
    left = (a % 2, b % 2)
    right = (c % 2, d % 2)
    if any(len(set(xs)) != len(xs) for xs in (colors, weak, left, right)):
        return 0
    return parity(colors) * parity(weak) * parity(left) * parity(right)


def alternating(indices):
    return sum(parity(p) * ordered(tuple(indices[i] for i in p))
               for p in permutations(range(4)))


def expand():
    result = defaultdict(int)
    for flavors, colors, weak, left, right in product(
        permutations(range(2)), permutations(range(3)), permutations(range(2)),
        permutations(range(2)), permutations(range(2)),
    ):
        term = (q(flavors[0], colors[0], weak[0], left[0]),
                q(flavors[1], colors[1], weak[1], left[1]),
                u(colors[2], right[0]), e(right[1]))
        monomial, sign = wedge(term)
        result[monomial] += sign * parity(colors) * parity(weak) * parity(left) * parity(right)
    return {m: c for m, c in result.items() if c}


class PairwiseAudit(unittest.TestCase):
    def test_full_expansion(self):
        actual = {m: c for m in combinations(range(32), 4) if (c := alternating(m))}
        self.assertEqual(actual, expand())
        self.assertEqual(len(actual), 48)
        self.assertEqual({abs(c) for c in actual.values()}, {2})

    def test_common_vector_diagonal(self):
        # Lean chooses a Q vector seen by both projections, here (1,1).
        value = sum(alternating((q(p, 0, 0, 0), q(r, 1, 1, 1), u(2, 0), e(1)))
                    for p, r in product(range(2), repeat=2))
        self.assertEqual(value, 4)

    def test_repetition_and_missing_pair(self):
        self.assertEqual(alternating((q(0, 0, 0, 0), q(0, 0, 0, 0), u(2, 0), e(1))), 0)
        self.assertEqual(alternating((q(0, 0, 0, 0), q(0, 1, 1, 1), u(2, 0), e(1))), 0)


if __name__ == "__main__":
    unittest.main()
