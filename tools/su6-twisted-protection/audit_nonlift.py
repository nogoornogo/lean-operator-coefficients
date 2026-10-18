"""Exact nonliftable UV inner C2 candidate; not a Lean certificate.

Reuses only the explicit component basis, mass and Lie/Grassmann utilities.
All scalar computations use integers modulo 4 or modulo 12.
"""

import unittest
from itertools import combinations, permutations

from audit_block_phase import (
    BASIS, INDEX, N, MASS, VEV, ROOTS, gaussian_mul, lie_action,
    rank, expand, WITNESS,
)


LIFT = (1, 1, 1, 3, 3, 3)  # fourth-root exponents
EXTERNAL = {"15": 0, "first": 1, "second": 1}


def lift_phase(v):
    return (sum(LIFT[a] for a in v[1:]) if v[0] == "15" else -LIFT[v[1]]) % 4


REMOVED = [EXTERNAL[v[0]] for v in BASIS]
PHASES = [(lift_phase(v) + EXTERNAL[v[0]]) % 4 for v in BASIS]
DEFECT = [0 if v[0] == "15" else 2 for v in BASIS]  # rho(-I)


def qque_phases():
    result = [PHASES[INDEX[("15", a, 3 + w)]]
              for a in range(3) for w in range(2) for _ in range(2)]
    for a in range(3):
        pair = tuple(b for b in range(3) if b != a)
        result.extend([-PHASES[INDEX[("15", *pair)]] % 4] * 2)
    result.extend([-PHASES[INDEX[("15", 3, 4)]] % 4] * 2)
    return result


def determinant(matrix):
    total = 0
    for p in permutations(range(6)):
        sign = (-1) ** sum(p[i] > p[j] for i in range(6) for j in range(i + 1, 6))
        term = sign
        for i in range(6):
            term *= matrix[i][p[i]]
        total += term
    return total


def centralizer_generators():
    generators = []
    for a, b in combinations(range(6), 2):
        diagonal = [(-1 if i in (a, b) else 1) for i in range(6)]
        generators.append([[diagonal[i] if i == j else 0 for j in range(6)]
                           for i in range(6)])
    for b in range(1, 6):
        matrix = [[int(i == j) for j in range(6)] for i in range(6)]
        matrix[0][0] = matrix[b][b] = 0
        matrix[0][b], matrix[b][0] = -1, 1
        generators.append(matrix)
    return generators


class NonliftAudit(unittest.TestCase):
    def test_full_matrix_centralizer_is_scalar(self):
        # A finite subset of actual SU(6) matrices already has scalar
        # centralizer. Hence so does SU(6); this makes the six-lift list complete.
        equations = []
        for matrix in centralizer_generators():
            self.assertEqual(determinant(matrix), 1)
            for a in range(6):
                for b in range(6):
                    self.assertEqual(sum(matrix[k][a] * matrix[k][b] for k in range(6)),
                                     int(a == b))
                    row = [int(a == i) * matrix[j][b] - matrix[a][i] * int(j == b)
                           for i in range(6) for j in range(6)]
                    if any(row):
                        self.assertEqual(sum(row[6 * i + i] for i in range(6)), 0)
                        equations.append(row)
        self.assertEqual(rank(equations), 35)  # 36 variables, scalar kernel

    def test_lift_and_physical_orders(self):
        self.assertEqual(sum(LIFT) % 4, 0)
        self.assertEqual([2 * a % 4 for a in LIFT], [2] * 6)  # s²=-I
        self.assertTrue(all(2 * a % 4 == 0 for a in PHASES))  # U²=1
        self.assertTrue(any(a != 0 for a in PHASES))  # exact order two
        self.assertEqual((LIFT[0] - LIFT[3]) % 4, 2)  # beta is nontrivial
        # beta² fixes every E_ab, since s² is scalar.
        self.assertTrue(all(2 * (a - b) % 4 == 0 for a in LIFT for b in LIFT))

    def test_all_central_corrections_fail(self):
        # All lifts of the same inner automorphism are z^k s, k=0,...,5.
        # In twelfth-root units, z is 2 and s has entries 3 or 9.
        # An SU(6) lift of C2 must have square exactly identity.
        lift12 = [3 * a for a in LIFT]
        failures = []
        for k in range(6):
            corrected = [(a + 2 * k) % 12 for a in lift12]
            self.assertEqual(sum(corrected) % 12, 0)
            square = [2 * a % 12 for a in corrected]
            self.assertEqual(len(set(square)), 1)
            self.assertNotEqual(square, [0] * 6)
            failures.append(square[0])
        self.assertEqual(failures, [6, 10, 2, 6, 10, 2])
        # Negative control: the previous block generator itself has order two,
        # so a test that rejected every C2 inner action would be incorrect.
        ordinary = (0, 0, 0, 2, 2, 0)
        self.assertTrue(all(2 * a % 4 == 0 for a in ordinary))

    def test_covariance_and_visible_defect(self):
        for a in range(6):
            for b in range(6):
                action = lie_action(a, b)
                for i in range(N):
                    for j in range(N):
                        if action[i][j]:
                            self.assertEqual((PHASES[i] - PHASES[j]) % 4,
                                             (LIFT[a] - LIFT[b]) % 4)
        # d(h,h)=(s s)^-1 s(1)=-I, and C(h)=rho(s^-1)U=E.
        self.assertEqual([2 * a % 4 for a in REMOVED], DEFECT)
        light = [j for j in range(N) if all(MASS[i][j] == 0 for i in range(N))]
        visible = [BASIS[j] for j in light if DEFECT[j] != 0]
        self.assertEqual(visible, [("first", a) for a in range(5)])
        self.assertNotEqual(DEFECT, [0] * N)

    def test_vacuum_mass_and_radical(self):
        for a in range(6):
            for b in range(6):
                entry = (VEV[a] if a == b else 0, 0)
                self.assertEqual(gaussian_mul(gaussian_mul(ROOTS[LIFT[a]], entry),
                                              ROOTS[-LIFT[b] % 4]), entry)
        # beta restricted to the standard SM subgroup is the identity.
        self.assertEqual(len(set(LIFT[:3])), 1)
        self.assertEqual(len(set(LIFT[3:5])), 1)
        self.assertEqual(N - rank(MASS), 15)
        for i in range(N):
            for j in range(N):
                if MASS[i][j]:
                    self.assertEqual((PHASES[i] + PHASES[j]) % 4, 0)
        self.assertEqual([PHASES[INDEX[("15", a, b)]] for a in range(3)
                          for b in range(3, 5)], [0] * 6)  # Q
        self.assertEqual([PHASES[INDEX[("15", a, b)]] for a, b in
                          ((0, 1), (0, 2), (1, 2), (3, 4))], [2] * 4)  # u^c,e^c
        self.assertEqual([PHASES[INDEX[("first", a)]] for a in range(5)],
                         [0, 0, 0, 2, 2])  # d^c,L

    def test_lorentz_grassmann_qque_survives(self):
        phases = qque_phases()
        self.assertEqual(phases, [0] * 12 + [2] * 8)
        polynomial = expand()
        self.assertEqual(len(polynomial), 24)
        self.assertEqual(polynomial[WITNESS], 2)
        for monomial in polynomial:
            self.assertEqual(sum(phases[j] for j in monomial) % 4, 0)
        # Both right-handed fields are odd; dropping only the e_R sign fails.
        bad = phases[:18] + [0, 0]
        self.assertTrue(all(sum(bad[j] for j in m) % 4 == 2 for m in polynomial))


if __name__ == "__main__":
    unittest.main()
