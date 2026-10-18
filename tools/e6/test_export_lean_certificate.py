"""Formatting controls for untrusted data emission; Lean checks the mathematics."""

from fractions import Fraction
import unittest

from export_lean_certificate import code, integer, vector


class LeanEmissionTests(unittest.TestCase):
    def test_integer_literals(self):
        self.assertEqual(integer(Fraction(6, 2)), "3")
        self.assertEqual(integer(-2), "(-2)")
        self.assertEqual(integer(0), "0")

    def test_nonintegral_rejected(self):
        with self.assertRaises(ValueError):
            integer(Fraction(1, 3))

    def test_stable_entry_order(self):
        self.assertEqual(code({(1, 0): -2, (0, 1): 1}),
                         "[((0, 1), 1), ((1, 0), (-2))]")

    def test_empty_code_and_vector(self):
        self.assertEqual(code({}), "[]")
        self.assertEqual(vector(["[]"]), "![\n  []]")


if __name__ == "__main__":
    unittest.main()
