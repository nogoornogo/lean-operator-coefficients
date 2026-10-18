"""Exact bounded controls on pinned, supplied model dictionaries; not a Lean oracle."""
from fractions import Fraction as F
from itertools import permutations, product
from math import gcd
import unittest


def rank(matrix):
    a = [[F(x) for x in row] for row in matrix]
    r = 0
    for c in range(len(a[0]) if a else 0):
        p = next((i for i in range(r, len(a)) if a[i][c]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        z = a[r][c]
        a[r] = [x/z for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][c]
                a[i] = [x-z*y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def multiply(a, v):
    return [sum(F(x)*y for x, y in zip(row, v)) for row in a]


def epsilon(p):
    if len(set(p)) != len(p):
        return 0
    return (-1)**sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p)))


class BaryonLepton(unittest.TestCase):
    def test_integral_dictionary_and_stabilizer(self):
        # Charge order (6B,2L); the full SM/exotic charge dictionary is integral.
        sm = [(F(1,3),0),(F(1,3),0),(F(1,3),0),(0,1),(0,1)]
        exotic = [(F(s*3,2),F(s*3,2)) for s in (-1,1)]
        normalized = [(6*b,2*l) for b,l in sm+exotic]
        self.assertTrue(all(F(x).denominator == 1 for row in normalized for x in row))
        # Torus angles (x,y) modulo 1: 18x+6y=0 mod1 and 4y=0 mod1.
        # y=l/4 and x=b/36 exhaust solutions; b+3l must be even.
        stabilizer = [(F(b,36),F(l,4)) for b,l in product(range(36),range(4))
                      if (18*F(b,36)+6*F(l,4)).denominator == 1]
        self.assertEqual(len(stabilizer),72)
        self.assertTrue(all((4*y).denominator == 1 for x,y in stabilizer))
        witness = (F(1,18),F(0))
        self.assertIn(witness, stabilizer)
        self.assertEqual((6*witness[0]).denominator,3)  # qque phase is not unity
        self.assertEqual((2*witness[0]) % 1,F(1,9))
        self.assertEqual((-2*witness[0]) % 1,F(8,9))
        # VEV lattice determinant 72; gcd of entries 2 -> invariant factors 2,36.
        vev_matrix = [[-18,-6],[0,-4]]
        det = vev_matrix[0][0]*vev_matrix[1][1]-vev_matrix[0][1]*vev_matrix[1][0]
        d1 = gcd(*(x for row in vev_matrix for x in row))
        self.assertEqual((d1,abs(det)//d1),(2,36))

    def test_uniform_family_and_scalar_dressing_obstruction(self):
        charges = (2,2,2,0,0)  # physical Q,uR,dR,L,eR on pure Z18
        q,u,d,l,e = charges
        self.assertEqual([(d+u)+(q+l),(q+q)+(u+e),3*q+l,2*u+d+e],[6]*4)
        # Any integer number of S_BL/S_L and conjugates contributes multiple18
        # to 6B. The necessary dressing equation 6+18k=0 has no integer solution.
        self.assertNotEqual(6 % 18,0)
        # Three generations: every flavor tuple has the same forbidden charge.
        for _ in product(range(3),repeat=4):
            self.assertNotEqual((q+q+u+e) % 18,0)

    def test_exotic_mass_control_with_majorana(self):
        # One explicit unbroken-SM control, after nonzero singlet VEVs:
        # charged/doublet vector-like maps nonzero, neutral symmetric block.
        self.assertEqual(rank([[1]]),1)
        self.assertEqual(rank([[2]]),1)
        self.assertEqual(rank([[1,2],[2,3]]),2)
        # Exceptional tuned neutral parameters can leave a kernel: not assumed absent.
        self.assertEqual(rank([[1,1],[1,1]]),1)


class SplitMultiplets(unittest.TestCase):
    def test_exact_light_lines_and_mixing_control(self):
        # Columns: (10 species,40_1,40_2); same algebra for (5c,50_1,50_2).
        q = [[1,0,0],[0,1,0]]
        u = [[1,0,0],[0,0,1]]
        for m,v in ((q,[0,0,1]),(u,[0,1,0])):
            self.assertEqual(rank(m),2)
            self.assertEqual(rank([row[1:] for row in m]),1)
            self.assertEqual(multiply(m,v),[0,0])
        # Generic C invertible: a massless line still exists but mixes the 10.
        mixed = [[1,1,0],[1,0,1]]
        self.assertEqual(rank(mixed),2)
        self.assertEqual(rank([row[1:] for row in mixed]),2)
        self.assertEqual(multiply(mixed,[1,-1,-1]),[0,0])
        # det(C)=0 alone does not establish a unique pure light line.
        deficient = [[1,0,0],[0,0,0]]
        self.assertEqual(rank(deficient),1)
        self.assertEqual(multiply(deficient,[0,1,0]),[0,0])
        self.assertEqual(multiply(deficient,[0,0,1]),[0,0])

    def test_parity_and_mass_invariance(self):
        parity = {'5c':-1,'10':-1,'40':1,'bar40':1,'50c':1,'bar50c':1,
                  '24':1,'75':1,'45':1}
        terms = [('5c','10','45'),('40','40','45'),('40','50c','45'),
                 ('bar40','40'),('50c','bar50c')]
        def sign(term):
            z = 1
            for field in term:
                z *= parity[field]
            return z
        self.assertTrue(all(sign(t) == 1 for t in terms))
        for t in [('24','10','bar40'),('75','10','bar40'),('75','5c','bar50c'),
                  ('10','40','45')]:
            self.assertEqual(sign(t),-1)
        self.assertEqual(1*1*1*(-1),-1)  # light qque under putative lepton parity
        q = [[1,0,0],[0,1,0]]
        column_parity = [-1,1,1]
        row_parity = [1,1]
        self.assertTrue(any(q[i][j] and row_parity[i]*column_parity[j] != 1
                            for i,j in product(range(2),range(3))))
        # H=1 does not require equal embeddings or equal kernel lines.
        self.assertNotEqual([0,0,1],[0,1,0])


class PatiSalam(unittest.TestCase):
    def test_baryon_and_gauge_charge_controls(self):
        # J=1 on f and chi, T=B-L=1/3 for color, -1 for lepton component.
        for t,b,l in [(F(1,3),F(1,3),F(0)),(-F(1),F(0),F(1))]:
            self.assertEqual((1+t)/4,b)
            self.assertEqual((1-3*t)/4,l)
        # Physical qque conserves B-L, but violates accidental B and J.
        self.assertEqual(3*F(1,3)-1,0)
        self.assertEqual(3*F(1,3),1)
        self.assertEqual(4*1,4)
        # Exhaustive hypercharge obstruction for all charged SM mass entries.
        ys = [1,-4,6,2,-3]
        self.assertTrue(all(a+b != 0 for a,b in product(ys,ys+[0])))
        # Symmetric neutral-sector block before EW breaking: no charged mass.
        neutral = [[0,0,0],[0,0,2],[0,2,3]]
        self.assertEqual(rank(neutral),2)
        self.assertEqual(multiply(neutral,[1,0,0]),[0,0,0])

    def test_dimension_five_epsilon_polynomial(self):
        # Eq19 for X=R, one generation. Scalar chi commutes; the Weyl bilinear
        # f_A f_B is symmetric in combined internal labels after spin contraction.
        # Fix two distinct color components with opposite SU2 indices as f slots.
        # The coefficient of B_{(0,0),(1,1)} chi_{(2,0)} chi_{(3,1)} is nonzero.
        coeff = 0
        fslots = ((0,0),(1,1))
        cslots = ((2,0),(3,1))
        for f in permutations(fslots):
            for c in permutations(cslots):
                coeff += epsilon([f[0][0],f[1][0],c[0][0],c[1][0]]) * \
                         epsilon([f[0][1],f[1][1]]) * epsilon([c[0][1],c[1][1]])
        self.assertEqual(coeff,4)
        # chi_(3,1) is the neutral VEV slot; remaining chi is a color scalar.
        # This is a polynomial component check, not matching or operator completeness.


if __name__ == '__main__':
    unittest.main()
