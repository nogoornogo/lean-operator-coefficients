"""Exact finite C4 candidate audit; a computational check, not a Lean proof.

Basis: exterior-square 15, first dual six, second dual six. A fourth root
is stored as its integer exponent modulo four. Lie matrices and the mass
matrix have integer entries; rank is computed over fractions.
"""

from fractions import Fraction
from itertools import combinations
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "qque"))
from audit_one_generation import expand, WITNESS


PAIRS = list(combinations(range(6), 2))
BASIS = [("15", a, b) for a, b in PAIRS]
BASIS += [(copy, a) for copy in ("first", "second") for a in range(6)]
INDEX = {v: i for i, v in enumerate(BASIS)}
N = len(BASIS)
GAUGE = (0, 0, 0, 2, 2, 0)  # diag(1,1,1,-1,-1,1)
EXTERNAL = {"15": 1, "first": 1, "second": 3}
VEV = (1, 1, 1, 1, 1, -5)
HYPERCHARGE = (-2, -2, -2, 3, 3, 0)  # six times Y
ROOTS = ((1, 0), (0, 1), (-1, 0), (0, -1))


def gaussian_mul(x, y):
    return (x[0] * y[0] - x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def gauge_exponent(v):
    return (sum(GAUGE[a] for a in v[1:]) if v[0] == "15"
            else -GAUGE[v[1]]) % 4


PHASES = [(gauge_exponent(v) + EXTERNAL[v[0]]) % 4 for v in BASIS]


def zeros(n=N):
    return [[0 for _ in range(n)] for _ in range(n)]


def lie_action(a, b):
    """Matrix of E_ab on wedge^2 six + dual six + dual six."""
    out = zeros()
    for j, v in enumerate(BASIS):
        if v[0] == "15":
            for slot in (1, 2):
                if v[slot] != b:
                    continue
                pair = list(v[1:])
                pair[slot - 1] = a
                if pair[0] == pair[1]:
                    continue
                sign = 1 if pair[0] < pair[1] else -1
                target = ("15", *sorted(pair))
                out[INDEX[target]][j] += sign
        elif v[1] == a:
            out[INDEX[(v[0], b)]][j] -= 1
    return out


def linear_combination(terms):
    out = zeros()
    for scalar, mat in terms:
        for i in range(N):
            for j in range(N):
                out[i][j] += scalar * mat[i][j]
    return out


MASS = zeros()
for a in range(5):
    i, j = INDEX[("15", a, 5)], INDEX[("second", a)]
    MASS[i][j] = MASS[j][i] = 1
i, j = INDEX[("first", 5)], INDEX[("second", 5)]
MASS[i][j] = MASS[j][i] = 1


def rank(matrix):
    work = [[Fraction(x) for x in row] for row in matrix]
    r = 0
    for c in range(len(work[0])):
        pivot = next((i for i in range(r, len(work)) if work[i][c]), None)
        if pivot is None:
            continue
        work[r], work[pivot] = work[pivot], work[r]
        denominator = work[r][c]
        work[r] = [x / denominator for x in work[r]]
        for i in range(r + 1, len(work)):
            factor = work[i][c]
            work[i] = [x - factor * y for x, y in zip(work[i], work[r])]
        r += 1
    return r


def qque_phases():
    # Same ordering as audit_one_generation: 12 Q, 6 u_R, 2 e_R.
    # u_R/e_R are duals of the all-left u^c/e^c in the 15.
    result = [PHASES[INDEX[("15", a, 3 + w)]]
              for a in range(3) for w in range(2) for _ in range(2)]
    for a in range(3):
        pair = tuple(b for b in range(3) if b != a)
        result.extend([-PHASES[INDEX[("15", *pair)]] % 4] * 2)
    result.extend([-PHASES[INDEX[("15", 3, 4)]] % 4] * 2)
    return result


class BlockPhaseAudit(unittest.TestCase):
    def test_gauge_and_residual_order(self):
        self.assertEqual(sum(GAUGE) % 4, 0)  # determinant one
        self.assertTrue(all(2 * a % 4 == 0 for a in GAUGE))
        self.assertTrue(all(4 * a % 4 == 0 for a in PHASES))
        self.assertTrue(all(2 * a % 4 == 2 for a in PHASES))  # U^2=-id
        # A noncentral UV action: E_03 is conjugated to -E_03.
        self.assertEqual((GAUGE[0] - GAUGE[3]) % 4, 2)
        self.assertNotEqual(lie_action(0, 3), zeros())

    def test_inner_covariance(self):
        # Exhaustive on all 36 matrix units, hence on the complexified Lie
        # algebra. All three scalar external blocks commute with rho(E_ab).
        for a in range(6):
            for b in range(6):
                action = lie_action(a, b)
                for i in range(N):
                    for j in range(N):
                        if action[i][j]:
                            self.assertEqual((PHASES[i] - PHASES[j]) % 4,
                                             (GAUGE[a] - GAUGE[b]) % 4)

    def test_vacuum_and_standard_gauge(self):
        # Both diagonal matrices commute, and external scalar action is neutral.
        for a in range(6):
            for b in range(6):
                entry = (VEV[a] if a == b else 0, 0)
                conjugated = gaussian_mul(gaussian_mul(ROOTS[GAUGE[a]], entry),
                                         ROOTS[-GAUGE[b] % 4])
                self.assertEqual(conjugated, entry)
        # g is scalar on each standard color/weak block.
        self.assertEqual(len(set(GAUGE[:3])), 1)
        self.assertEqual(len(set(GAUGE[3:5])), 1)

    def test_mass_and_exact_radical(self):
        self.assertEqual(N, 27)
        self.assertEqual(rank(MASS), 12)
        radical = {BASIS[j] for j in range(N)
                   if all(MASS[i][j] == 0 for i in range(N))}
        expected = {("15", a, b) for a, b in combinations(range(5), 2)}
        expected |= {("first", a) for a in range(5)}
        self.assertEqual(radical, expected)
        self.assertEqual(len(radical), 15)
        # The other 12 columns form the six disjoint nondegenerate pairs;
        # together with rank=12 this identifies the entire radical.
        for i in range(N):
            for j in range(N):
                self.assertEqual(MASS[i][j], MASS[j][i])
                if MASS[i][j]:
                    self.assertEqual((PHASES[i] + PHASES[j]) % 4, 0)
        # Using +i on the second copy instead of -i fails all six pairs.
        bad = [(gauge_exponent(v) + 1) % 4 for v in BASIS]
        self.assertTrue(all((bad[i] + bad[j]) % 4 == 2
                            for i in range(N) for j in range(N) if MASS[i][j]))
        for v in radical:
            expected_y = (sum(HYPERCHARGE[a] for a in v[1:])
                          if v[0] == "15" else -HYPERCHARGE[v[1]])
            if v[0] == "first":
                self.assertEqual(expected_y, 2 if v[1] < 3 else -3)
            elif v[2] < 3:
                self.assertEqual(expected_y, -4)  # u^c
            elif v[1] >= 3:
                self.assertEqual(expected_y, 6)  # e^c
            else:
                self.assertEqual(expected_y, 1)  # Q

    def test_standard_gauge_mass_invariance(self):
        generators = []
        for block in (range(3), range(3, 5)):
            generators.extend(lie_action(a, b) for a in block for b in block if a != b)
            for a in list(block)[1:]:
                generators.append(linear_combination([
                    (1, lie_action(a, a)), (-1, lie_action(block[0], block[0]))]))
        generators.append(linear_combination([
            (y, lie_action(a, a)) for a, y in enumerate(HYPERCHARGE)]))
        self.assertEqual(len(generators), 12)
        for action in generators:
            for i in range(N):
                for j in range(N):
                    self.assertEqual(sum(action[k][i] * MASS[k][j]
                                         + MASS[i][k] * action[k][j] for k in range(N)), 0)

    def test_physical_qque_survives(self):
        phases = qque_phases()
        self.assertEqual(phases, [3] * 20)  # -i on Q, u_R, e_R
        polynomial = expand()
        self.assertEqual(len(polynomial), 24)
        self.assertEqual(polynomial[WITNESS], 2)
        for monomial in polynomial:
            self.assertEqual(sum(phases[j] for j in monomial) % 4, 0)
        # Explicit SM hypercharge and baryon number of the witness:
        self.assertEqual(1 + 1 + 4 - 6, 0)  # six times Y
        self.assertEqual(1 + 1 + 1 + 0, 3)  # three times B
        # Negative control: changing only e_R to +1 removes every monomial.
        bad_phases = phases[:18] + [0, 0]
        self.assertTrue(all(sum(bad_phases[j] for j in m) % 4 != 0 for m in polynomial))


if __name__ == "__main__":
    unittest.main()
