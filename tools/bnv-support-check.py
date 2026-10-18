#!/usr/bin/env python3
"""Exact arithmetic cross-check; not a Lean completeness certificate.

Enumerate the signed matter/Higgs necessary conditions through dimension 11.
No third-party dependencies. Run: python3 tools/bnv-support-check.py
"""
from collections import Counter
from itertools import combinations_with_replacement

Y = (1, 4, -2, -3, -6, -1, -4, 2, 3, 6)
B = (1, 1, 1, 0, 0, -1, -1, -1, 0, 0)
L = (0, 0, 0, 1, 1, 0, 0, 0, -1, -1)
LEFT = (1, 0, 0, 1, 0, 0, 1, 1, 0, 1)
NAMES = ("q", "u", "d", "l", "e", "cq", "cu", "cd", "cl", "ce")


def inventory(bound):
    result = []
    for n in range(0, 2 * bound // 3 + 1):
        if n % 2:
            continue
        for labels in combinations_with_replacement(range(10), n):
            baryon = sum(B[s] for s in labels)
            if baryon <= 0 or baryon % 3 or sum(LEFT[s] for s in labels) % 2:
                continue
            for h in range((2 * bound - 3 * n) // 2 + 1):
                for ch in range((2 * bound - 3 * n - 2 * h) // 2 + 1):
                    if sum(Y[s] for s in labels) + 3 * h - 3 * ch:
                        continue
                    counts = tuple(labels.count(s) for s in range(10))
                    result.append((3 * n // 2 + h + ch, baryon // 3,
                                   sum(L[s] for s in labels), counts, h, ch))
    return result


def main():
    rows = inventory(11)
    expected_seven = {
        ((0, 1, 2, 0, 0, 0, 0, 0, 1, 0), 0, 1),
        ((2, 0, 1, 0, 0, 0, 0, 0, 1, 0), 0, 1),
        ((1, 0, 2, 0, 0, 0, 0, 0, 0, 1), 0, 1),
        ((0, 0, 3, 0, 0, 0, 0, 0, 1, 0), 1, 0),
    }
    assert {(c, h, ch) for d, _, _, c, h, ch in rows if d == 7} == expected_seven
    assert all(d >= 6 and sum(c) in (4, 6) and b in (1, 2)
               for d, b, _, c, _, _ in rows)
    print("Positive-baryon arithmetic candidates; conjugates not duplicated.")
    for (d, b, l), count in sorted(Counter((d, b, l) for d, b, l, *_ in rows).items()):
        print(f"dimension={d}, deltaB={b}, deltaL={l}: {count} types")
    print(f"Total: {len(rows)} arithmetic types. Local invariants/statistics not checked.")


if __name__ == "__main__":
    main()
