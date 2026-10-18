"""Exact local D.38 sign check in the normalized dictionary, not an amplitude proof.

Paper slot order Q,Q,E,U pairs electron then up spinors. Compare its Grassmann
expansion with the independently expanded repository Q,Q,U,E contraction.
No derivatives, numerical approximations or package runtime are used.
"""
from collections import defaultdict
from itertools import permutations, product
import unittest

from audit_one_generation import e, expand, parity, q, u, wedge, WITNESS


def paper_expand(include_fermi_sign=True):
    result = defaultdict(int)
    for colors, weak, left, right in product(
        permutations(range(3)), permutations(range(2)),
        permutations(range(2)), permutations(range(2)),
    ):
        # right[0] is E in printed slot 3, right[1] is U in slot 4.
        slots = (q(colors[0], weak[0], left[0]),
                 q(colors[1], weak[1], left[1]),
                 e(right[0]), u(colors[2], right[1]))
        if include_fermi_sign:
            monomial, sign = wedge(slots)
        else:
            # Negative control: reordering these last two fermions without parity.
            monomial, sign = wedge((slots[0], slots[1], slots[3], slots[2]))
        result[monomial] += sign * parity(colors) * parity(weak) * parity(left) * parity(right)
    return {m: c for m, c in result.items() if c}


class LiD38Audit(unittest.TestCase):
    def test_full_component_expansion(self):
        self.assertEqual(paper_expand(), expand())

    def test_omitted_fermi_sign_control(self):
        self.assertEqual(paper_expand(False), {m: -c for m, c in expand().items()})
        self.assertNotEqual(paper_expand(False), expand())

    def test_raw_alternatization_normalization(self):
        self.assertEqual(paper_expand()[WITNESS], 2)
        self.assertEqual(len(paper_expand()), 24)


if __name__ == '__main__':
    unittest.main()
