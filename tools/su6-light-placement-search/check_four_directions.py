"""Four bounded exact coordinate screens; not Lean or full-group certificates."""
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'su6-twisted-protection'))
import audit_block_phase as base

Y = [sum(base.HYPERCHARGE[i] for i in v[1:]) if v[0] == '15'
     else -base.HYPERCHARGE[v[1]] for v in base.BASIS]
TEN = [i for i,v in enumerate(base.BASIS) if v[0] == '15' and 5 not in v[1:]]


def mass_at(j):
    m = base.zeros()
    for i in range(6):
        if i == j:
            continue
        k = base.INDEX[('15', *sorted((i,j)))]
        l = base.INDEX[('second', i)]
        sign = 1 if i < j else -1
        m[k][l] = m[l][k] = sign
    k,l = base.INDEX[('first', j)],base.INDEX[('second', j)]
    m[k][l] = m[l][k] = 1
    return m


def invariant(m, generator):
    return all(sum(generator[k][i]*m[k][j]+m[i][k]*generator[k][j]
                   for k in range(base.N)) == 0
               for i in range(base.N) for j in range(base.N))


def gauge_generators():
    # Complexified color/weak off-diagonal roots and diagonal Cartan/hypercharge.
    gs = [base.lie_action(i,j) for block in (range(3),range(3,5))
          for i in block for j in block if i != j]
    for h in ((1,-1,0,0,0,0),(0,1,-1,0,0,0),(0,0,0,1,-1,0),base.HYPERCHARGE):
        gs.append(base.linear_combination([(h[i],base.lie_action(i,i)) for i in range(6)]))
    return gs


class FourDirections(unittest.TestCase):
    def test_vev(self):
        accepted = []
        for j in range(6):
            m = mass_at(j)
            self.assertEqual(base.rank(m),12)
            if all(invariant(m,g) for g in gauge_generators()):
                accepted.append(j)
        self.assertEqual(accepted,[5])
        print('VEV: 6 coordinate directions, rank 12 each; only coordinate 6 preserves standard SM')

    def test_maximal_scalar_screen(self):
        # For any bilinear invariant under the hypercharge Lie generator,
        # (Yi+Yj) Mij=0. Every relevant row has no admissible column.
        forced = [i for i in range(base.N) if all(Y[i]+y != 0 for y in Y)]
        self.assertEqual(forced,TEN)
        allowed = [(i,j) for i in range(base.N) for j in range(i,base.N) if Y[i]+Y[j]==0]
        self.assertEqual(len(allowed),29)
        self.assertEqual(base.rank(mass_at(5)),12)
        # Universal rank upper bound: 27 minus these ten forced-zero rows.
        self.assertEqual(len(TEN),10)
        print('SCALAR: all hypercharge-invariant symmetric matrices (29 permitted entries) retain the 10 standard components')

    def test_vectorlike_placement(self):
        # Two fifteen copies A,B and one conjugate C. For each species, its
        # conjugate must pair with a copy of opposite residual charge. Select
        # one paired copy; the other is the unique surviving component.
        admitted = splits = charged = 0
        enlarged_y = Y + Y[:15] + [-q for q in Y[:15]]
        species_of = lambda v: (0 if v[1]<3<=v[2]<5 else
                                1 if v[2]<3 else 2)
        example_checked = False
        for qa,qb,qc in product(range(4),repeat=3):
            for paired in product((0,1),repeat=3):  # Q,uc,ec
                charges=(qa,qb)
                if not all((charges[i]+qc)%4==0 for i in paired):
                    continue
                admitted += 1
                # One split representative is extended to a complete 57-field
                # paired mass. Other counts refer only to Q/uc/ec admission.
                if (qa,qb,qc) == (0,0,0) and paired == (0,0,1):
                    edges = [(i,j) for i in range(base.N) for j in range(i+1,base.N)
                             if base.MASS[i][j]]
                    for k,v in enumerate(base.BASIS[:15]):
                        copy = paired[species_of(v)] if k in TEN else 1
                        edges.append((k if copy == 0 else 27+k,42+k))
                    used=[i for edge in edges for i in edge]
                    self.assertEqual(len(set(used)),42)
                    self.assertEqual(len(edges),21)
                    self.assertTrue(all(enlarged_y[i]+enlarged_y[j]==0 for i,j in edges))
                    matrix=[[0]*57 for _ in range(57)]
                    for i,j in edges: matrix[i][j]=matrix[j][i]=1
                    self.assertEqual(base.rank(matrix),42)
                    example_checked=True
                light=[charges[1-i] for i in paired]
                if len(set(paired))>1:
                    splits += 1
                    self.assertEqual(qa,qb)
                if (2*light[0]-light[1]-light[2])%4:
                    charged += 1
        self.assertTrue(example_checked)
        self.assertEqual((admitted,splits,charged),(56,24,0))
        print('PLACEMENT: 512 Z4 charge/placement cases; 56 admitted, 24 splits, none charge-forbid qque')

    def test_outside_scalar_block(self):
        phases=[0]*base.N
        for i,v in enumerate(base.BASIS):
            if v[0]=='15' and v[1]<3 and v[2]<3:
                phases[i]=1  # uc phase; Q/ec neutral
        self.assertTrue(all((phases[i]+phases[j])%4==0
                            for i in range(base.N) for j in range(base.N) if base.MASS[i][j]))
        for g in gauge_generators():
            self.assertTrue(all((phases[i]-phases[j])%4==0
                                for i in range(base.N) for j in range(base.N) if g[i][j]))
        old=base.PHASES
        try:
            base.PHASES=phases
            spin_phases=base.qque_phases()
        finally:
            base.PHASES=old
        poly=base.expand()
        self.assertTrue(poly)
        self.assertEqual({sum(spin_phases[i] for i in monomial)%4 for monomial in poly},{3})
        # A root-diagonal inner action must give one ratio for every occurrence
        # of rho(E03). Here the same root sees incompatible phase differences.
        g=base.lie_action(0,3)
        differences={(phases[i]-phases[j])%4 for i in range(base.N)
                     for j in range(base.N) if g[i][j]}
        self.assertGreater(len(differences),1)
        print(f'RESIDUAL: SM/mass-compatible C4 phases charge-forbid qque; E03 root-diagonal UV covariance fails: {sorted(differences)}')


if __name__ == '__main__':
    unittest.main()
