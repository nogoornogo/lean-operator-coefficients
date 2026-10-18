"""Exact finite qque statistics cross-check, not a Lean proof or UV model.

Expand epsilon_color * epsilon_weak * epsilon_left * epsilon_right in a
one-generation Grassmann algebra. There are 12 Q, 6 u_R and 2 e_R component
generators. No flavor index or interaction coefficient is postulated.
"""

from collections import defaultdict
from itertools import combinations, permutations, product
import unittest


def parity(indices):
    inversions = sum(a > b for i, a in enumerate(indices) for b in indices[i + 1 :])
    return (-1) ** inversions


def wedge(indices):
    """Canonical increasing monomial and its sign, or zero for repetition."""
    if len(set(indices)) != len(indices):
        return tuple(sorted(indices)), 0
    return tuple(sorted(indices)), parity(indices)


def q(color, weak, spin):
    return 4 * color + 2 * weak + spin


def u(color, spin):
    return 12 + 2 * color + spin


def e(spin):
    return 18 + spin


def expand():
    result = defaultdict(int)
    for colors, weak, left, right in product(
        permutations(range(3)), permutations(range(2)),
        permutations(range(2)), permutations(range(2)),
    ):
        monomial, sign = wedge((
            q(colors[0], weak[0], left[0]),
            q(colors[1], weak[1], left[1]),
            u(colors[2], right[0]), e(right[1]),
        ))
        result[monomial] += sign * parity(colors) * parity(weak) * parity(left) * parity(right)
    return {monomial: coefficient for monomial, coefficient in result.items() if coefficient}


WITNESS = (q(0, 0, 0), q(1, 1, 1), u(2, 0), e(1))


def ordered_symmetric_coefficient(indices):
    """Scalar version of QqueSpinorExterior.ordered with identity flavor splits."""
    a, b, c, d = indices
    if not (a < 12 and b < 12 and 12 <= c < 18 and 18 <= d < 20):
        return 0
    colors = (a // 4, b // 4, (c - 12) // 2)
    weak = ((a // 2) % 2, (b // 2) % 2)
    left = (a % 2, b % 2)
    right = ((c - 12) % 2, d - 18)
    if any(len(set(xs)) != len(xs) for xs in (colors, weak, left, right)):
        return 0
    # The unnormalized symmetric flavor coefficient is 1*1 + 1*1.
    return 2 * parity(colors) * parity(weak) * parity(left) * parity(right)


def alternating_symmetric_coefficient(indices):
    """All 4! slot permutations, as in FourSlotAlternation.alternating."""
    return sum(parity(s) * ordered_symmetric_coefficient(tuple(indices[i] for i in s))
               for s in permutations(range(4)))


class OneGenerationAudit(unittest.TestCase):
    def test_relations(self):
        self.assertEqual(wedge((0, 0))[1], 0)
        self.assertEqual(wedge((0, 1)), ((0, 1), 1))
        self.assertEqual(wedge((1, 0)), ((0, 1), -1))

    def test_expansion(self):
        polynomial = expand()
        self.assertEqual(len(polynomial), 24)
        self.assertEqual({abs(c) for c in polynomial.values()}, {2})
        self.assertEqual(polynomial[WITNESS], 2)

    def test_selected_component_projection(self):
        selected = set(WITNESS)
        projected = {m: c for m, c in expand().items() if set(m) <= selected}
        self.assertEqual(projected, {WITNESS: 2})

    def test_full_alternation_correspondence(self):
        actual = {m: v for m in combinations(range(20), 4)
                  if (v := alternating_symmetric_coefficient(m))}
        self.assertEqual(actual, {m: 2 * v for m, v in expand().items()})
        self.assertEqual(actual[WITNESS], 4)
        self.assertEqual(alternating_symmetric_coefficient((0, 0, u(2, 0), e(1))), 0)


if __name__ == "__main__":
    unittest.main()
