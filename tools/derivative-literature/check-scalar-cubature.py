#!/usr/bin/env python3
"""Independent exact checks of the displayed 36-wave data and normalization.

Reads the Gaussian-integer literals in the Lean source, not a generated rank
or paper count. This is supplementary evidence; all theorem premises and
moment identities must still be checked by Lean. Standard library only.
"""
from functools import reduce
from itertools import permutations, product
from pathlib import Path
import json
import re

SOURCE = Path(__file__).resolve().parents[2] / 'Math/Algebra/ScalarFourWaveCubature/Basic.lean'


def add(x, y):
    return x[0]+y[0], x[1]+y[1]


def mul(x, y):
    return x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0]


def prod(xs):
    return reduce(mul, xs, (1, 0))


def moment(k, r, i, j, l, m):
    slots = [[[], [], [], [i,j,l,m]], [[], [], [i,j,l], [m]],
             [[], [], [i,j], [l,m]], [[], [i,j], [l], [m]],
             [[i], [j], [l], [m]]][r]
    return reduce(add, (prod(prod(k[s][v] for v in vs) for s, vs in zip(p, slots))
                        for p in permutations(range(4))), (0, 0))


def metric(i, j):
    return 0 if i != j else 1 if i == 0 else -1


def main():
    raw = SOURCE.read_text().split('def raw', 1)[1].split('def metric', 1)[0]
    pairs = [tuple(map(int, p)) for p in re.findall(r'⟨(-?\d+),(-?\d+)⟩', raw)]
    assert len(pairs) == 36*4*4
    configurations = [[pairs[a*16+s*4:a*16+s*4+4] for s in range(4)] for a in range(36)]
    for k in configurations:
        for i in range(4):
            assert reduce(add, (s[i] for s in k), (0, 0)) == (0, 0)
        for s in k:
            square = [mul(x, x) for x in s]
            assert (square[0][0]-sum(x[0] for x in square[1:]),
                    square[0][1]-sum(x[1] for x in square[1:])) == (0, 0)
    alpha, beta = [0,0,-768,384,1152], [0,0,1536,-768,1152]
    for r in range(5):
        for i, j, l, m in product(range(4), repeat=4):
            value = reduce(add, (moment(k,r,i,j,l,m) for k in configurations), (0, 0))
            expect = (alpha[r]*metric(i,j)*metric(l,m)+
                      beta[r]*(metric(i,l)*metric(j,m)+metric(i,m)*metric(j,l)))
            assert value == (expect, 0), (r,i,j,l,m,value,expect)
    witness = sum(metric(i,i)*metric(j,j)*
                  sum(moment(k,4,i,i,j,j)[0] for k in configurations)
                  for i in range(4) for j in range(4))
    assert witness == 27648
    # Removing one summand preserves its null/conserving hypotheses but breaks
    # the invariant moment identity, so data completeness is actually tested.
    assert any(reduce(add, (moment(k,0,i,i,i,i) for k in configurations[1:]), (0,0)) != (0,0)
               for i in range(4))
    print(json.dumps(dict(role='exact supplementary check; not a Lean premise',
                         configurations=36, conservation_checks=144, null_checks=144,
                         rank_four_moment_checks=1280, normalized_K_squared_value='1',
                         omission_control='detected'), indent=2))


if __name__ == '__main__':
    main()
