"""Regression tests for the external candidate generator, not formal proofs."""

import unittest

from lie_certificate import Span, bracket, sparse_matrix


class CandidateArithmeticTests(unittest.TestCase):
    def test_bracket_orientation(self):
        e, f = {(0, 1): 1}, {(1, 0): 1}
        self.assertEqual(bracket(e, f), {(0, 0): 1, (1, 1): -1})
        self.assertEqual(bracket(f, e), {(0, 0): -1, (1, 1): 1})
        self.assertEqual(bracket(e, e), {})

    def test_exact_dependent_rows(self):
        span = Span()
        span.insert({(0, 0): 2, (1, 1): 1}, {"test": 0})
        span.insert({(1, 1): 3}, {"test": 1})
        span.insert({(0, 0): 4, (1, 1): 5}, {"test": 2})
        self.assertEqual(len(span.basis), 2)
        self.assertEqual(span.coordinates({(0, 0): 4, (1, 1): 5}), {0: 2, 1: 1})

    def test_out_of_order_pivots(self):
        span = Span()
        span.insert({(2, 2): 1}, {"test": 0})
        span.insert({(0, 0): 2, (2, 2): 1}, {"test": 1})
        self.assertEqual(span.coordinates({(0, 0): 2}), {0: -1, 1: 1})

    def test_reject_outside_span(self):
        span = Span()
        span.insert({(0, 0): 1}, {"test": 0})
        with self.assertRaises(ValueError):
            span.coordinates({(0, 1): 1})

    def test_reject_duplicate_entries(self):
        with self.assertRaises(ValueError):
            sparse_matrix([[0, 1, 1], [0, 1, 2]])

    def test_reject_invalid_entries(self):
        for entries in [[[27, 0, 1]], [[0, 0, 0]], [[0, 0, 0.5]]]:
            with self.assertRaises(ValueError):
                sparse_matrix(entries)


if __name__ == "__main__":
    unittest.main()
