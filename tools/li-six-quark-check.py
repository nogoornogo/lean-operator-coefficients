"""Exact exploratory local rank check for Li 2007.07899v1 (5.63).

No third-party dependencies. This is not a Lean proof or a physical C-matrix
dictionary. Slots here are the paper order D,D,D,D,U,U. All values are exact
integers/rationals. Tests both row/column composition conventions explicitly.
"""
from fractions import Fraction
from itertools import permutations, product
from math import gcd
from functools import reduce
import json
import sys


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i+1, len(p)))


def compose(p, q):
    return tuple(p[q[i]] for i in range(6))


def subgroup(blocks):
    out = []
    for choices in product(*(list(permutations(b)) for b in blocks)):
        p = list(range(6))
        for b, c in zip(blocks, choices):
            for i, j in zip(b, c):
                p[i] = j
        out.append(tuple(p))
    return out


def eps(v):
    return sign(v) if sorted(v) == list(range(len(v))) else 0


colors = [((0,1,2),(3,4,5)), ((0,1,3),(2,4,5)),
          ((0,1,4),(2,3,5)), ((0,2,3),(1,4,5)), ((0,2,4),(1,3,5))]
spins = [((0,1),(2,3),(4,5)), ((0,1),(2,5),(3,4)),
         ((0,3),(1,2),(4,5)), ((0,5),(1,2),(3,4)), ((0,5),(1,4),(2,3))]


def value(pairs, v):
    z = 1
    for p in pairs:
        z *= eps([v[i] for i in p])
    return z


def rank(rows):
    pivots = {}
    for row in rows:
        v = list(map(Fraction, row))
        for j, p in sorted(pivots.items()):
            if v[j]:
                c = v[j]
                v = [a-c*b for a,b in zip(v,p)]
        j = next((j for j,x in enumerate(v) if x), None)
        if j is not None:
            c = v[j]
            pivots[j] = [x/c for x in v]
    return len(pivots)


def probes(pairs, n):
    chosen, rows = [], []
    for v in product(range(n), repeat=6):
        row = [value(p,v) for p in pairs]
        if rank(rows+[row]) > len(rows):
            chosen.append(v)
            rows.append(row)
        if len(rows) == 5:
            return chosen
    raise AssertionError("local five-dimensional basis not found")


cp, sp = probes(colors,3), probes(spins,2)
local_probes = list(product(cp,sp))
group = subgroup([(0,1,2,3),(4,5)])
assert len(group) == 48
seed_colors = [((0,2,4),(1,3,5)), ((0,3,5),(1,2,4)),
               ((0,2,4),(1,3,5)), ((0,3,5),(1,2,4)),
               ((0,2,4),(1,3,5)), ((0,1,4),(2,3,5)),
               ((0,3,5),(1,2,4)), ((0,2,4),(1,3,5)),
               ((0,1,5),(2,3,4)), ((0,2,4),(1,3,5))]
seed_spin = ((0,3),(4,1),(5,2))
shapes = [(3,1),(3,1),(2,1,1),(2,1,1),(4,),(4,),
          (3,1),(2,2),(2,2),(2,1,1)]


def young(k, reverse):
    rows, start = [], 0
    for size in shapes[k]:
        rows.append(tuple(range(start,start+size)))
        start += size
    cols = [tuple(row[j] for row in rows if j < len(row)) for j in range(max(shapes[k]))]
    up_rows, up_cols = ([(4,),(5,)],[(4,5)]) if k < 4 else ([(4,5)],[(4,),(5,)])
    terms = []
    for r in subgroup(rows+up_rows):
        for c in subgroup(cols+up_cols):
            p = compose(c,r) if reverse else compose(r,c)
            # Moving flavor permutation onto local slots includes the Fermi sign.
            terms.append((sign(c)*sign(p),p))
    return terms


def evaluation(k, terms, orbit):
    out = []
    for c,s in local_probes:
        z = 0
        for a,p in terms:
            q = compose(orbit,p)
            z += a*value(seed_colors[k],tuple(c[q[i]] for i in range(6))) * value(
                seed_spin,tuple(s[q[i]] for i in range(6)))
        out.append(z)
    return out


def inverse(a):
    n = len(a)
    a = [list(map(Fraction,row))+[Fraction(i == j) for j in range(n)]
         for i,row in enumerate(a)]
    for j in range(n):
        k = next(k for k in range(j,n) if a[k][j])
        a[j],a[k] = a[k],a[j]
        d = a[j][j]
        a[j] = [x/d for x in a[j]]
        for k in range(n):
            if k != j:
                d = a[k][j]
                a[k] = [x-d*y for x,y in zip(a[k],a[j])]
    return [row[n:] for row in a]


def certificate():
    # Convert paper probe inputs to repository U,D,U,D,D,D order.
    repo_to_paper = (4,0,5,1,2,3)
    b = [[value(c,tuple(cv[repo_to_paper[i]] for i in range(6))) *
          value(s,tuple(sv[repo_to_paper[i]] for i in range(6)))
          for c in colors for s in spins] for cv,sv in local_probes]
    bi = inverse(b)
    def coordinates(vals):
        return [sum(x*y for x,y in zip(row,vals)) for row in bi]
    identity = tuple(range(6))
    terms = [young(k,False) for k in range(10)]
    terms.append([(sign(g[4:]),g) for g in group])
    seeds = [coordinates(evaluation(k if k < 10 else 0,t,identity))
             for k,t in enumerate(terms)]
    divisors = [reduce(gcd,(int(x) for x in row)) for row in seeds]
    seeds = [[x/d for x in row] for row,d in zip(seeds,divisors)]
    rows, selected = [], []
    for k,t in enumerate(terms):
        for j,g in enumerate(group):
            row = [x/divisors[k] for x in coordinates(evaluation(k if k < 10 else 0,t,g))]
            if rank(rows+[row]) > len(rows):
                rows.append(row)
                selected.append([k,j])
    assert len(rows) == 25
    a = [list(row) for row in zip(*rows)]
    ai = inverse(a)
    for left, right in [(a, ai), (ai, a)]:
        assert all(sum(left[i][k] * right[k][j] for k in range(25)) == int(i == j)
                   for i in range(25) for j in range(25))
    coeffs = []
    for t in terms:
        coeffs.append([sum(c for c,p in t if p == g) for g in group])
    return {"group": group, "young": coeffs, "divisors": divisors,
            "seeds": seeds, "selected": selected, "basis": a, "inverse": ai}


if __name__ == "__main__":
    if "--certificate-json" in sys.argv:
        print(json.dumps(certificate(),default=str))
        sys.exit(0)
    identity = tuple(range(6))
    certificate()  # Check the proposed two-sided rational inverse as well.
    local_basis = [[value(c,cv)*value(s,sv) for cv,sv in local_probes]
                   for c in colors for s in spins]
    assert rank(local_basis) == 25
    raw = [evaluation(k,[(1,identity)],g) for k in range(10) for g in group]
    print({"local_basis_rank": rank(local_basis), "raw_seed_orbit_rank": rank(raw)})
    # Flavor shape (1,1,1,1) for D and (2) for U: after Fermi transfer,
    # this is the local character trivial on S4 and sign on S2.
    missing_terms = [(sign(g[4:]),g) for g in group]
    missing = evaluation(0,missing_terms,identity)
    for reverse in [False, True]:
        projected = [evaluation(k,young(k,reverse),identity) for k in range(10)]
        orbit = [evaluation(k,young(k,reverse),g) for k in range(10) for g in group]
        assert rank(projected) == 10
        assert rank(orbit) == 24
        assert any(missing) and rank(orbit+[missing]) == 25
        print({"composition": "column-row" if reverse else "row-column",
               "projected_seed_rank": rank(projected), "orbit_rank": rank(orbit),
               "projected_nonzero": [any(v) for v in projected],
               "extra_character_nonzero": any(missing),
               "orbit_with_extra_rank": rank(orbit+[missing])})
