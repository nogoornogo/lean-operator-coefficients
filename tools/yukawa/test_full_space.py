"""Independent controls for untrusted exact coordinate results."""
import unittest
from fractions import Fraction as Q
from itertools import product
from full_space import (add_entry, character_check, commutator_equations, compute,
                        echelon, kernel, scalar_model, vacuum_and_mass_basis)


def compose(a, b):
    out = [dict() for _ in b]
    for j, col in enumerate(b):
        for k, c in col.items():
            for i, d in a[k].items():
                add_entry(out[j], i, c * d)
    return out


def bracket(a, b):
    ab, ba = compose(a, b), compose(b, a)
    for x, y in zip(ab, ba):
        for i, c in y.items():
            add_entry(x, i, -c)
    return ab


def full_matrix(pairs, vector, dimension=27):
    rows = [dict() for _ in range(dimension)]
    for k, c in vector.items():
        i, j = pairs[k]
        if i == j:
            add_entry(rows[i], i, 2 * c)
        else:
            add_entry(rows[i], j, c)
            add_entry(rows[j], i, c)
    return rows


class FullSpaceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.result, cls.data = compute()

    def test_exact_dimensions(self):
        r = self.result
        self.assertEqual((r['weight_preserving_variables'], r['equation_rank'],
                          r['commutant_dimension'], r['vacuum_image_dimension'],
                          r['evaluation_kernel_dimension']), (1704, 1682, 22, 5, 17))

    def test_elimination_and_mutation(self):
        rows = [{0: 1, 1: 2}, {0: 2, 1: 4}, {1: 1, 2: 1}]
        self.assertEqual(kernel(echelon(rows), 3), [{2: Q(1), 1: Q(-1), 0: Q(2)}])
        _, _, _, rows, basis, _, _ = self.data
        bad = dict(basis[0])
        add_entry(bad, 0, 1)
        self.assertTrue(any(sum(c * bad.get(i, 0) for i, c in row.items()) for row in rows))

    def test_all_off_diagonal_generators(self):
        # Solve with simple generators, verify against every E_ab independently.
        _, _, variables, _, basis, _, _ = self.data
        _, _, _, gen = scalar_model()
        for a, b in product(range(6), repeat=2):
            if a == b:
                continue
            rows = commutator_equations(variables, gen(a, b))
            for v in basis:
                self.assertTrue(all(sum(c * v.get(i, 0) for i, c in row.items()) == 0 for row in rows))

    def test_lie_action_conventions(self):
        _, _, weights, gen = scalar_model()
        for i in range(5):
            h = bracket(gen(i, i + 1), gen(i + 1, i))
            expected = [{k: w[i] - w[i + 1]} if w[i] != w[i + 1] else {}
                        for k, w in enumerate(weights)]
            self.assertEqual(h, expected)
        for i in range(4):
            self.assertEqual(bracket(gen(i, i + 1), gen(i + 1, i + 2)), gen(i, i + 2))

    def test_character_collision_control(self):
        # For SU(3), exterior^2(3) = bar3: the same construction has dimension 45, not 22.
        _, _, weights, _ = scalar_model(3)
        self.assertEqual(character_check(weights)[1], 45)

    def test_vacuum_stabilizer_coordinates(self):
        matter, pairs, _, gen = scalar_model()
        vacuum, _ = vacuum_and_mass_basis(matter, pairs)
        for a, b in product(range(5), repeat=2):
            if a == b:
                continue
            out = {}
            for j, c in vacuum.items():
                for i, d in gen(a, b)[j].items():
                    add_entry(out, i, c * d)
            self.assertEqual(out, {})

    def test_structural_block_support(self):
        matter, pairs, _, _, _, _, image = self.data
        mid = {x: i for i, x in enumerate(matter)}
        for k, v in enumerate(image):
            actual = full_matrix(pairs, v)
            expected = [dict() for _ in matter]
            if k < 2:
                for i in range(5):
                    a, b = mid[("w", i, 5)], mid[("b", k, i)]
                    expected[a][b] = expected[b][a] = Q(1)
            else:
                f, g = [(0, 0), (0, 1), (1, 1)][k - 2]
                a, b = mid[("b", f, 5)], mid[("b", g, 5)]
                expected[a][b] = expected[b][a] = Q(1)
            self.assertEqual(actual, expected)

    def test_rank_strata_samples(self):
        # Sampling checks the formula, not exhaustiveness; Lean proves the small-block ranks.
        _, pairs, _, _, _, _, image = self.data
        seen = set()
        for a, b, u, v, w in product((-1, 0, 1), repeat=5):
            vector = {}
            for c, direction in zip((a, b, u, v, w), image):
                for i, d in direction.items():
                    add_entry(vector, i, c * d)
            rank_singlet = 0 if u == v == w == 0 else (1 if u*w == v*v else 2)
            expected_rank = (10 if a or b else 0) + rank_singlet
            rank = len(echelon(full_matrix(pairs, vector)))
            self.assertEqual(rank, expected_rank)
            seen.add(27 - rank)
        self.assertEqual(seen, {15, 16, 17, 25, 26, 27})


if __name__ == '__main__':
    unittest.main()
