"""Exact finite SM-sector mass controls. No Lean oracle or UV coupling claim."""
from fractions import Fraction as F
import unittest

# Integral hypercharges 6Y in the existing all-left SU5 branching.
SPECIES = {'Q': (6, 1), 'uc': (3, -4), 'ec': (1, 6),
           'dc': (3, 2), 'L': (2, -3)}
TEN = ('Q', 'uc', 'ec')


def rank(a):
    a = [[F(x) for x in row] for row in a]
    if not a:
        return 0
    r = 0
    for col in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        z = a[r][col]
        a[r] = [x / z for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][col]
                a[i] = [x - z * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def extended_mass(rows):
    """Two ten copies and one dual ten, with unchanged chiral bar-five.

    Per species use the canonical SM evaluation pairing with row (alpha,beta).
    This is a broken-phase mass ansatz, without an asserted UV Yukawa origin.
    """
    indices, charges = {}, []
    for name, (dim, charge) in SPECIES.items():
        copies = (0, 1, 'dual') if name in TEN else (0,)
        for copy in copies:
            indices[name, copy] = list(range(len(charges), len(charges) + dim))
            charges.extend([(-charge if copy == 'dual' else charge)] * dim)
    a = [[F(0) for _ in charges] for _ in charges]
    for name in TEN:
        for copy, value in enumerate(rows[name]):
            for i, j in zip(indices[name, copy], indices[name, 'dual']):
                a[i][j] = a[j][i] = F(value)
    return a, indices, charges


class MassPatterns(unittest.TestCase):
    def test_chiral_pairing_exhaustion(self):
        weights = [q for dim, q in SPECIES.values() for _ in range(dim)]
        self.assertEqual(len(weights), 15)
        self.assertTrue(all(x + y != 0 for x in weights for y in weights))
        # Same exhaustive obstruction for the fixed two-copy chiral control.
        self.assertTrue(all(x + y != 0 for x in weights * 2 for y in weights * 2))

    def test_unmixed_nonzero_mass(self):
        a, _, qs = extended_mass({s: (0, 1) for s in TEN})
        self.assertEqual(len(a), 35)
        self.assertEqual(rank(a), 20)
        self.assertEqual(len(a) - rank(a), 15)
        self.assertTrue(all(not a[i][j] or qs[i] + qs[j] == 0
                            for i in range(35) for j in range(35)))

    def test_mixed_radical(self):
        rows = {'Q': (1, 0), 'uc': (0, 1), 'ec': (1, 1)}
        a, ids, qs = extended_mass(rows)
        self.assertEqual(rank(a), 20)
        self.assertTrue(all(a[i][j] == a[j][i] for i in range(35) for j in range(35)))
        self.assertTrue(all(not a[i][j] or qs[i] + qs[j] == 0
                            for i in range(35) for j in range(35)))
        for name, (alpha, beta) in rows.items():
            # (-beta, alpha) in each SM component is an actual null vector.
            for i, j in zip(ids[name, 0], ids[name, 1]):
                v = [F(0)] * 35
                v[i], v[j] = -F(beta), F(alpha)
                self.assertTrue(all(sum(x * y for x, y in zip(row, v)) == 0 for row in a))
        # No shared copy line survives in all three species.
        self.assertEqual(rank(list(rows.values())), 2)

    def test_two_copy_block_swap(self):
        # H=C2: c=1,w=-1,a=-1; s=diag(1,1,1,-1,-1) is in SU5.
        # Copy swap A gives Q=A, uc=-A, ec=-A, all genuine C2 actions.
        swap = [[0, 1], [1, 0]]
        self.assertEqual(1**3 * (-1)**2, 1)
        def mm(a, b):
            return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]
        def kron(a, b):
            return [[a[i][j]*b[k][l] for j in range(2) for l in range(2)]
                    for i in range(2) for k in range(2)]
        ident = [[int(i == j) for j in range(2)] for i in range(2)]
        self.assertEqual(mm(swap, swap), ident)
        neg = [[-x for x in row] for row in swap]
        self.assertEqual(mm(neg, neg), ident)
        qq, ue = kron(swap, swap), kron(neg, neg)
        sym = [[int(i == j) + int((i//2, i%2) == (j%2, j//2))
                for j in range(4)] for i in range(4)]
        self.assertEqual(mm(ue, sym), mm(sym, qq))
        self.assertEqual(sym[0][0], 2)
        # Both occupied copy eigencharacters satisfy physical qque neutrality.
        for r in (-1, 1):
            self.assertEqual(r*r*(-r)*(-r), 1)

    def test_affine_splitting_rows(self):
        # Defined coefficient ansatz M + y*(4,-1,-6), not a UV-coupling proof.
        labels = {'uc': 4, 'Q': -1, 'ec': -6}
        rows = {name: (label, 1) for name, label in labels.items()}
        a, ids, _ = extended_mass(rows)
        self.assertEqual(rank(a), 20)
        for name, (alpha, beta) in rows.items():
            for i, j in zip(ids[name, 0], ids[name, 1]):
                v = [F(0)] * 35
                v[i], v[j] = F(beta), -F(alpha)
                self.assertTrue(all(sum(x*y for x, y in zip(row, v)) == 0 for row in a))
        self.assertEqual(rank(list(rows.values())), 2)
        # One zero row after an affine cancellation: uc alpha=beta=0.
        partial, _, _ = extended_mass({name: (label - 4, 0) for name, label in labels.items()})
        self.assertEqual(35 - rank(partial), 21)

    def test_rank_and_mass_controls(self):
        zero, _, _ = extended_mass({s: (0, 0) for s in TEN})
        self.assertEqual(rank(zero), 0)
        partial, _, _ = extended_mass({'Q': (0, 1), 'uc': (0, 0), 'ec': (0, 1)})
        self.assertEqual(35 - rank(partial), 21)
        # Independent exact elimination regression.
        self.assertEqual(rank([[1, 2], [2, 4]]), 1)
        self.assertEqual(rank([[1, 2], [2, 3]]), 2)


if __name__ == '__main__':
    unittest.main()
