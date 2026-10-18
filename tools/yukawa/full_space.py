"""Exact, untrusted SU(6) coordinate calculation; no numerical sampling.

Matter basis: e_i wedge e_j (i<j), then two labelled dual fundamentals.
Scalar basis: x_i*x_j (i<=j) in Sym^2(V*).
Polynomial coefficients encode B(x,x)/2: diagonal matrix entries are twice
the square coefficient; off-diagonal entries equal the mixed coefficient.
"""

from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import combinations, combinations_with_replacement
import argparse
import json


def clean(row):
    return {i: x for i, x in row.items() if x}


def add_entry(row, i, x):
    row[i] = row.get(i, 0) + x
    if not row[i]:
        del row[i]


def canonical(w):
    return tuple(x - w[-1] for x in w)


def product(a, b):
    out = Counter()
    for x, cx in a.items():
        for y, cy in b.items():
            out[canonical(tuple(i + j for i, j in zip(x, y)))] += cx * cy
    return clean(out)


def representation(n=6):
    basis = [("w", i, j) for i, j in combinations(range(n), 2)]
    basis += [("b", f, i) for f in range(2) for i in range(n)]
    index = {v: i for i, v in enumerate(basis)}
    weights = []
    for kind, i, j in basis:
        w = [0] * n
        if kind == "w":
            w[i] += 1
            w[j] += 1
        else:
            w[j] -= 1
        weights.append(tuple(w))

    def generator(a, b):
        cols = [dict() for _ in basis]
        for k, (kind, i, j) in enumerate(basis):
            if kind == "w":
                for u, v, c in [(a, j, int(i == b)), (i, a, int(j == b))]:
                    if c and u != v:
                        add_entry(cols[k], index[("w", min(u, v), max(u, v))],
                                  c if u < v else -c)
            elif j == a:
                cols[k][index[("b", i, b)]] = -1
        return cols

    return basis, weights, generator


def scalar_model(n=6):
    matter, weights, gen = representation(n)
    pairs = list(combinations_with_replacement(range(len(matter)), 2))
    index = {v: i for i, v in enumerate(pairs)}
    scalar_weights = [canonical(tuple(-x - y for x, y in zip(weights[i], weights[j])))
                      for i, j in pairs]

    def generator(a, b):
        dual = [dict() for _ in matter]
        for j, col in enumerate(gen(a, b)):
            for i, c in col.items():
                dual[i][j] = -c
        cols = [dict() for _ in pairs]
        for k, (i, j) in enumerate(pairs):
            for t, c in dual[i].items():
                add_entry(cols[k], index[tuple(sorted((t, j)))], c)
            for t, c in dual[j].items():
                add_entry(cols[k], index[tuple(sorted((i, t)))], c)
        return cols

    return matter, pairs, scalar_weights, generator


def character_check(weights):
    n = len(weights[0])
    char = Counter(weights)
    den = {tuple([0] * n): 1}
    for i, j in combinations(range(n), 2):
        root = [0] * n
        root[i], root[j] = -1, 1
        den = product(den, {tuple([0] * n): 1, canonical(root): -1})
    dominant = []
    for w, multiplicity in product(char, den).items():
        if all(w[i] >= w[i + 1] for i in range(n - 1)):
            dimension = Q(1)
            for i, j in combinations(range(n), 2):
                dimension *= Q(w[i] - w[j] + j - i, j - i)
            assert dimension.denominator == 1 and multiplicity > 0
            dominant.append((tuple(w[i] - w[i + 1] for i in range(n - 1)),
                             int(dimension), multiplicity))
    dual = {canonical(tuple(-x for x in w)): c for w, c in char.items()}
    end = product(char, dual)
    ct = sum(c * end.get(canonical(tuple(-x for x in w)), 0) for w, c in den.items())
    assert sum(d * m for _, d, m in dominant) == len(weights)
    assert ct == sum(m * m for _, _, m in dominant)
    return sorted(dominant), ct


def echelon(rows):
    pivots = {}
    for source in rows:
        row = {i: Q(c) for i, c in source.items() if c}
        while row:
            p = min(row)
            if p not in pivots:
                c = row[p]
                pivots[p] = {i: x / c for i, x in row.items()}
                break
            c = row[p]
            for i, x in pivots[p].items():
                add_entry(row, i, -c * x)
    return pivots


def kernel(pivots, variables):
    free = sorted(set(range(variables)) - pivots.keys())
    vectors = []
    for f in free:
        v = {f: Q(1)}
        for p in sorted(pivots, reverse=True):
            c = -sum(x * v.get(i, 0) for i, x in pivots[p].items() if i != p)
            if c:
                v[p] = c
        vectors.append(v)
    return vectors


def commutator_equations(variables, gen):
    # Each row is an entry of T*gen - gen*T, linear in the entries of T.
    rows = defaultdict(dict)
    inverse = defaultdict(list)
    for j, col in enumerate(gen):
        for i, c in col.items():
            inverse[i].append((j, c))
    for k, (i, j) in enumerate(variables):
        for b, c in inverse[j]:
            add_entry(rows[(i, b)], k, c)
        for a, c in gen[i].items():
            add_entry(rows[(a, j)], k, -c)
    return [row for _, row in sorted(rows.items()) if row]


def vacuum_and_mass_basis(matter, pairs, n=6):
    mid = {x: i for i, x in enumerate(matter)}
    pid = {x: i for i, x in enumerate(pairs)}
    vectors = []
    for f in range(2):
        vectors.append({pid[tuple(sorted((mid[("w", i, n - 1)], mid[("b", f, i)])))]: Q(1)
                        for i in range(n - 1)})
    for f, g in [(0, 0), (0, 1), (1, 1)]:
        vectors.append({pid[tuple(sorted((mid[("b", f, n - 1)], mid[("b", g, n - 1)])))]:
                        Q(1, 2) if f == g else Q(1)})
    vacuum = dict(vectors[1])
    for i, c in vectors[3].items():
        add_entry(vacuum, i, c)
    return vacuum, vectors


def compute():
    matter, pairs, weights, gen = scalar_model()
    by_weight = defaultdict(list)
    for i, w in enumerate(weights):
        by_weight[w].append(i)
    variables = sorted((i, j) for block in by_weight.values() for i in block for j in block)
    generators = [(i, i + 1) for i in range(5)] + [(i + 1, i) for i in range(5)]
    rows = [r for a, b in generators for r in commutator_equations(variables, gen(a, b))]
    pivots = echelon(rows)
    basis = kernel(pivots, len(variables))
    assert all(sum(c * v.get(i, 0) for i, c in row.items()) == 0
               for v in basis for row in rows)
    assert len(echelon(basis)) == len(basis)
    constituents, character_dimension = character_check(weights)
    assert len(basis) == character_dimension == 22
    vacuum, expected_image = vacuum_and_mass_basis(matter, pairs)
    image = []
    for v in basis:
        out = {}
        for k, c in v.items():
            i, j = variables[k]
            add_entry(out, i, c * vacuum.get(j, 0))
        image.append(out)
    image_rank = len(echelon(image))
    assert image_rank == len(echelon(expected_image)) == 5
    assert len(echelon(image + expected_image)) == 5
    result = {"matter_dimension": len(matter), "scalar_dimension": len(pairs),
              "weight_preserving_variables": len(variables), "commutator_equations": len(rows),
              "equation_rank": len(pivots), "commutant_dimension": len(basis),
              "constituents_dynkin_dimension_multiplicity": constituents,
              "vacuum_image_dimension": image_rank, "evaluation_kernel_dimension": len(basis) - image_rank}
    return result, (matter, pairs, variables, rows, basis, image, expected_image)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--candidate', action='store_true', help='also emit exact sparse basis data')
    args = parser.parse_args()
    result, data = compute()
    if args.candidate:
        matter, pairs, variables, rows, basis, image, expected = data

        def encode(v):
            return [[i, Q(c).numerator, Q(c).denominator] for i, c in sorted(v.items())]

        result['candidate'] = {'matter_basis': matter, 'scalar_pairs': pairs,
                               'variables': variables, 'commutant_basis': list(map(encode, basis)),
                               'echelon': [[i, encode(r)] for i, r in sorted(echelon(rows).items())],
                               'vacuum_images': list(map(encode, image)),
                               'mass_basis': list(map(encode, expected))}
    print(json.dumps(result, indent=2))
