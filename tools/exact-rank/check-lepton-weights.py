#!/usr/bin/env python3
"""Exact diagnostics for the uniform Lean L multiplicity formula.

This script is a regression aid, not a Lean certificate or a CSV classifier.
No output here is used as a theorem premise.
"""
from fractions import Fraction
from itertools import combinations

SLOTS = [(a, b) for a in (-1, 1) for b in (-1, 1) for _ in range(3)]


def a1_extraction(weight: int) -> Fraction:
    if weight == 0:
        return Fraction(1)
    if abs(weight) == 2:
        return Fraction(-1, 2)
    return Fraction(0)


def multiplicity(n: int, m: int) -> Fraction:
    result = Fraction(0)
    for subset in combinations(SLOTS, n):
        weak = sum(slot[0] for slot in subset)
        spin = sum(slot[1] for slot in subset)
        for j in range(m + 1):
            result += a1_extraction(weak + 2 * j - m) * a1_extraction(spin)
    return result


def main() -> None:
    for m in range(13):
        assert multiplicity(0, m) == int(m == 0), (0, m)
        assert multiplicity(12, m) == int(m == 0), (12, m)
    for n in range(13):
        for m in range(13):
            value = multiplicity(n, m)
            assert value.denominator == 1 and value >= 0, (n, m, value)
            if n % 2:
                assert value == 0, (n, m, value)
    assert multiplicity(2, 2) == 6
    print("169 exact degree pairs: zero/top, parity, integrality, positivity, LLHH checks passed")


if __name__ == "__main__":
    main()
