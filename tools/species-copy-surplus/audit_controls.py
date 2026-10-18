"""Exact finite controls for the surplus inlet; no Lean premise or UV model claim."""
from fractions import Fraction as F
from itertools import product
import unittest


def rank(matrix):
    a = [[F(x) for x in row] for row in matrix]
    r = 0
    for j in range(len(a[0]) if a else 0):
        p = next((i for i in range(r, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[p], a[r] = a[r], a[p]
        z = a[r][j]
        a[r] = [x/z for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][j]
                a[i] = [x-z*y for x,y in zip(a[i],a[r])]
        r += 1
    return r


def mv(matrix, vector):
    return [sum(F(x)*y for x,y in zip(row,vector)) for row in matrix]


def symmetric_mass(m, n_source, neutral):
    """Canonical source/opposite/rest presentation with no prohibited pairings."""
    n_target, n_rest = len(m), len(neutral)
    n = n_source+n_target+n_rest
    b = [[F(0) for _ in range(n)] for _ in range(n)]
    for j,row in enumerate(m):
        for i,x in enumerate(row):
            b[i][n_source+j] = b[n_source+j][i] = F(x)
    for i,row in enumerate(neutral):
        for j,x in enumerate(row):
            b[n_source+n_target+i][n_source+n_target+j] = F(x)
    return b


class SurplusControls(unittest.TestCase):
    def test_unequal_species_with_distinct_kernel_directions(self):
        q,u = [[1,0,0],[0,1,0]], [[0,1,0],[0,0,1]]
        self.assertEqual(3-rank(q),1)
        self.assertEqual(3-rank(u),1)
        self.assertEqual(mv(q,[0,0,1]),[0,0])
        self.assertEqual(mv(u,[1,0,0]),[0,0])
        self.assertEqual(rank(q+u),3)  # no common coordinate vector required
        # e:1->0 has its independent nonzero kernel.
        self.assertEqual(1-rank([]),1)

    def test_all_small_rectangular_masses(self):
        # Exhaustive finite diagnostic: 729 integer 2x3 masses, not all complex M.
        for entries in product((-1,0,1),repeat=6):
            m = [entries[:3],entries[3:]]
            self.assertGreaterEqual(3-rank(m),1)
            b = symmetric_mass(m,3,[[1,2],[2,3]])
            self.assertEqual(rank(b),2*rank(m)+2)
            self.assertTrue(all(b[i][j] == b[j][i] for i,j in product(range(7),repeat=2)))

    def test_hom_surplus_with_nontrivial_copy_actions(self):
        # H=C2; Hom from sign R has dimension equal to sign multiplicity.
        sources = [[1,1,-1],[1,-1,-1],[1]]
        targets = [[1],[-1,-1],[]]
        for a,c in zip(sources,targets):
            self.assertGreater(a.count(1),c.count(1))
        q,u = [[1,0,0]], [[0,1,0],[0,0,1]]
        for a,c,m in zip(sources,targets,[q,u,[]]):
            self.assertTrue(all(not m[j][i] or a[i] == c[j]
                                for j in range(len(c)) for i in range(len(a))))
        self.assertEqual(mv(q,[0,1,0]),[0])
        self.assertEqual(mv(u,[1,0,0]),[0,0])

    def test_dimension_difference_without_shared_constituent(self):
        sources = [[1],[1],[-1]]
        self.assertTrue(all(len(a)>0 for a in sources))
        self.assertFalse(any(all(a.count(r)>0 for a in sources) for r in (1,-1)))
        self.assertEqual(1*1*1*(-1),-1)  # qque is odd in this control

    def test_surplus_not_necessary_for_permission(self):
        # No common R, but qque is even: sufficient condition is not an iff.
        sources = [[1],[-1],[-1]]
        self.assertFalse(any(all(a.count(r)>0 for a in sources) for r in (1,-1)))
        self.assertEqual(1*1*(-1)*(-1),1)
        # Zero mass can retain kernels even with equal or reverse dimensions.
        self.assertEqual(1-rank([[0]]),1)
        self.assertEqual(1-rank([[0],[0]]),1)

    def test_neutral_majorana_sector_does_not_change_selected_kernel(self):
        m = [[1,0,0],[0,1,0]]
        for neutral in ([[1,2],[2,3]],[[1,1],[1,1]]):
            b = symmetric_mass(m,3,neutral)
            self.assertEqual(mv(b,[0,0,1,0,0,0,0]),[0]*7)
            self.assertEqual(rank(b),4+rank(neutral))
        # Forbidden source/rest mixing would destroy this chosen zero mode.
        bad = symmetric_mass(m,3,[[1,2],[2,3]])
        bad[2][5] = bad[5][2] = F(1)
        self.assertNotEqual(mv(bad,[0,0,1,0,0,0,0]),[0]*7)


if __name__ == '__main__':
    unittest.main()
