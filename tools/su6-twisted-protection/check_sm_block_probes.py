#!/usr/bin/env python3
"""Exact integer signed-Weyl probe scan, not a full normalizer classification.

Run: python3 tools/su6-twisted-protection/check_sm_block_probes.py
All 720 coordinate permutations are scanned. Four actual signed SU(3)/SU(2)
transpositions test forbidden cross-block entries in the standard SM image.
The finite result supplements the Lean color/weak witness; it is no oracle
for continuous actions, other embeddings, masses or protecting models.
"""
from itertools import permutations
import unittest


def identity():
    return tuple(tuple(int(i == j) for j in range(6)) for i in range(6))


def transpose(a):
    return tuple(zip(*a))


def multiply(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(6))
                       for j in range(6)) for i in range(6))


def parity(p):
    return (-1) ** sum(p[i] > p[j] for i in range(6) for j in range(i + 1, 6))


def representative(p):
    # Row convention agrees with Equiv.Perm.permMatrix: nonzero at (i,p(i)).
    return tuple(tuple((parity(p) if i == 0 else 1) if j == p[i] else 0
                       for j in range(6)) for i in range(6))


def signed_swap(a, b):
    p = list(range(6))
    p[a], p[b] = p[b], p[a]
    return tuple(tuple((-1 if i == a else 1) if j == p[i] else 0
                       for j in range(6)) for i in range(6))


def block(i):
    return 0 if i < 3 else 1 if i < 5 else 2


def no_cross_entries(a):
    return all(a[i][j] == 0 for i in range(6) for j in range(6)
               if block(i) != block(j))


PROBES = tuple(signed_swap(a, b) for a, b in ((0, 1), (0, 2), (1, 2), (3, 4)))


def passes(w):
    return all(no_cross_entries(multiply(multiply(w, c), transpose(w))) for c in PROBES)


class ProbeChecks(unittest.TestCase):
    def test_lean_witness_and_order(self):
        w, c = signed_swap(0, 3), signed_swap(0, 2)
        self.assertEqual(multiply(multiply(w, c), transpose(w))[3][2], -1)
        self.assertFalse(passes(w))
        self.assertEqual(multiply(multiply(w, w), multiply(w, w)), identity())
        self.assertNotEqual(multiply(w, w), identity())

    def test_all_720_representatives(self):
        survivors = []
        total = 0
        for p in permutations(range(6)):
            total += 1
            w = representative(p)
            self.assertEqual(multiply(w, transpose(w)), identity())
            # Permutation determinant times the one diagonal correction is +1.
            self.assertEqual(parity(p) * parity(p), 1)
            good = passes(w)
            self.assertEqual(good, all(block(i) == block(p[i]) for i in range(6)))
            if good:
                survivors.append(p)
        self.assertEqual(total, 720)
        self.assertEqual(len(survivors), 12)
        print("720 signed representatives: 12 pass probes, 708 fail.")

    def test_identity_and_internal_swaps(self):
        self.assertTrue(passes(identity()))
        self.assertTrue(passes(signed_swap(0, 2)))
        self.assertTrue(passes(signed_swap(3, 4)))


if __name__ == "__main__":
    unittest.main()
