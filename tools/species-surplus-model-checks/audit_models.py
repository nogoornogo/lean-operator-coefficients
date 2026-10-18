"""Exact checks on supplied pre-EW irreducible SM and residual dictionaries."""
from collections import Counter
from itertools import product
from pathlib import Path
import importlib.util
import sys
import unittest

sys.dont_write_bytecode = True

# Reuse the parent's rational matrix checks, without a new dependency.
spec = importlib.util.spec_from_file_location(
    'surplus_controls', Path(__file__).resolve().parents[1] / 'species-copy-surplus/audit_controls.py')
controls = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controls)
rank, mv, symmetric_mass = controls.rank, controls.mv, controls.symmetric_mass

# Irreducible labels (SU3 Dynkin p,q; SU2 dimension; integral 6Y).
Q, UC, EC, DC, L, N = (1,0,2,1), (0,1,1,-4), (0,0,1,6), (0,1,1,2), (0,0,2,-3), (0,0,1,0)
def dual(g):
    p,q,w,y = g
    return q,p,w,-y

TEN = [EC,Q,UC]
FIVEC = [L,DC]
FORTY = [Q,UC,(0,0,2,-9),(0,1,3,-4),(1,1,1,6),(0,2,2,1)]
FIFTYC = [DC,(0,0,1,12),(1,0,2,7),(2,0,3,2),(0,2,1,-8),(1,1,2,-3)]
SPLIT = TEN + FIVEC + 2*(FORTY + [dual(g) for g in FORTY]) + 2*(FIFTYC + [dual(g) for g in FIFTYC])
PS = [Q,UC,EC,DC,L,N,N]  # nuc and xi are neutral, independent masses allowed.

# Hom dimensions for a complex character R of Z_n (or an integral U1 weight).
# All entries are copy weights, not dimensions of the gauge carrier.
def surplus(a,c,r):
    return a.count(r)-c.count(r)

def common(a,c,candidates):
    return [r for r in candidates if all(surplus(x,y,r)>0 for x,y in zip(a,c))]

class ModelChecks(unittest.TestCase):
    def test_split_full_branching_and_pairing_dictionary(self):
        # Eq1: 10 + 5c + two vector-like 40/50 pairs, 375 internal dimensions.
        def dim(g):
            p,q,w,_ = g
            return (p+1)*(q+1)*(p+q+2)//2*w
        self.assertEqual(sum(map(dim,SPLIT)),375)
        counts = Counter(SPLIT)
        self.assertEqual([(counts[g],counts[dual(g)]) for g in (Q,UC,EC)],[(3,2),(3,2),(1,0)])
        for g in (Q,UC,EC):
            self.assertNotEqual(g,dual(g))  # No self pairing.
            rest = [h for h in SPLIT if h not in (g,dual(g))]
            self.assertTrue(all(h != dual(g) for h in rest))
        self.assertEqual(common([[0]*3,[0]*3,[0]],[ [0]*2,[0]*2,[]],[0]),[0])

    def test_split_arbitrary_block_controls(self):
        # All 729 bounded integer matrices; arbitrary complex M handled by Lean.
        for entries in product((-1,0,1),repeat=6):
            m = [entries[:3],entries[3:]]
            self.assertGreaterEqual(3-rank(m),1)
        q,u = [[1,0,0],[0,1,0]], [[1,0,0],[0,0,1]]
        for m,v in ((q,[0,0,1]),(u,[0,1,0])):
            self.assertEqual(mv(m,v),[0,0])
            self.assertEqual(mv(symmetric_mass(m,3,[[1]]),v+[0,0,0]),[0]*6)
        # Light-origin tuning is unnecessary for the surplus, unlike UV coupling claims.
        mixed = [[1,1,0],[1,0,1]]
        self.assertEqual(mv(mixed,[1,-1,-1]),[0,0])

    def test_split_light_vs_full_parity(self):
        # Light (+,+,-) obstructs shared R. Full Eq22 includes the odd 10 quarks.
        self.assertEqual(common([[0],[0],[1]],[[],[],[]],range(2)),[])
        full_a,full_c = [[1,0,0],[1,0,0],[1]], [[0,0],[0,0],[]]
        self.assertEqual(common(full_a,full_c,range(2)),[1])
        q = [[1,0,0],[0,1,0]]
        self.assertTrue(any(q[j][i] and full_a[0][i] != full_c[0][j]
                            for j,i in product(range(2),range(3))))
        # If full parity really is imposed, forbidden mixing vanishes and Q10 survives.
        invariant = [[0,1,0],[0,0,1]]
        self.assertEqual(mv(invariant,[1,0,0]),[0,0])
        self.assertEqual((2*1-1-1)%2,0)  # shared odd R permits qque.

    def test_ps_charged_and_majorana_dictionary(self):
        counts = Counter(PS)
        self.assertEqual([(counts[g],counts[dual(g)]) for g in (Q,UC,EC)],[(1,0)]*3)
        for g in (Q,UC,EC):
            self.assertTrue(all(g[3]+h[3] != 0 for h in PS))
        self.assertEqual(common([[0],[0],[0]],[[],[],[]],[0]),[0])
        # Selected charged zero modes survive every tested neutral symmetric mass.
        for a,b,c in product((-1,0,1),repeat=3):
            mass = [[0]*5 for _ in range(5)]
            mass[3][3],mass[3][4],mass[4][3],mass[4][4] = a,b,b,c
            for k in range(3):
                self.assertEqual(mv(mass,[int(i==k) for i in range(5)]),[0]*5)
        # Optional exact U1_B: integral 3B on the all-left copies.
        self.assertEqual(common([[1],[-1],[0]],[[],[],[]],[-1,0,1]),[])
        self.assertNotEqual(2*1-(-1)-0,0)  # physical qque has 3B=3.

    def test_bl_full_charged_copy_dictionary(self):
        # N=1, Y1=-1/2,Y2=-1. Both all-left eta entries have b=9 mod18.
        # Exotic etaR^c is an extra ec copy; etaL is its gauge partner.
        a,c = [[2],[16],[0,9]], [[],[],[9]]
        self.assertEqual(common(a,c,range(18)),[])
        self.assertEqual([surplus(a[2],c[2],r) for r in (0,9)],[1,0])
        self.assertNotEqual((2*2-16-0)%18,0)
        # Neutral and charged exotics cannot supply a common Q/uc constituent.
        exotics = [(0,0,2,-3),(0,0,2,3),dual(EC),EC,N,N]
        self.assertTrue(all(g not in (Q,UC,dual(Q),dual(UC)) for g in exotics))

if __name__ == '__main__':
    unittest.main()
