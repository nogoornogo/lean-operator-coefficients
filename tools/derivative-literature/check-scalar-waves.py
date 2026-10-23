#!/usr/bin/env python3
"""Independent exact four-wave validation; no finite-rank code is imported.

Direct sparse polynomial expansion checks free EOM/IBP rows, contraction and
paper normalizations, and assumption-removal controls. This is a diagnostic,
not a Lean premise, invariant-dual certificate or scattering calculation.
Python standard library only; no files or caches are written.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, permutations
import json

ZERO = (0, 0, 0, 0)
UNIT = tuple(tuple(int(i == j) for i in range(4)) for j in range(4))
ETA = (1, -1, -1, -1)
TARGET = (1, 1, 1, 1)


def add(*polynomials):
    out = {}
    for p in polynomials:
        for a, c in p.items():
            out[a] = out.get(a, Q(0)) + c
    return {a: c for a, c in out.items() if c}


def scale(c, p):
    return {a: c*v for a, v in p.items() if c*v}


def multiply(*polynomials):
    out = {ZERO: Q(1)}
    for p in polynomials:
        nxt = {}
        for a, c in out.items():
            for b, v in p.items():
                key = tuple(x+y for x, y in zip(a, b))
                nxt[key] = nxt.get(key, Q(0)) + c*v
        out = {a: c for a, c in nxt.items() if c}
    return out


def coefficient(p):
    return p.get(TARGET, Q(0))


def compositions(total, size):
    if size == 1:
        yield (total,)
    else:
        for n in range(total + 1):
            for rest in compositions(total-n, size-1):
                yield (n,) + rest


@lru_cache(None)
def monomials(fields, derivatives):
    # Ordered derivative allocations on all 4*fields coordinates, followed
    # by deduplication of commuting field factors. Independent of rank code.
    return sorted({tuple(sorted(tuple(a[4*i:4*i+4]) for i in range(fields)))
                   for a in compositions(derivatives, 4*fields)})


def shift(a, i, count=1):
    return tuple(v + (count if j == i else 0) for j, v in enumerate(a))


def dot(a, b):
    return sum(e*x*y for e, x, y in zip(ETA, a, b))


def paper_polynomials(momenta):
    # P4 sums distinct terms; s_ij = p_i dot p_j, without a factor of two.
    p1 = sum(dot(momenta[i], momenta[j])**2 for i, j in combinations(range(4), 2))
    p2 = sum(dot(momenta[i], momenta[j])*dot(momenta[i], momenta[k])
             for i in range(4) for j, k in combinations([r for r in range(4) if r != i], 2))
    p3 = (dot(momenta[0], momenta[1])*dot(momenta[2], momenta[3]) +
          dot(momenta[0], momenta[2])*dot(momenta[1], momenta[3]) +
          dot(momenta[0], momenta[3])*dot(momenta[1], momenta[2]))
    return p1, p2, p3


def evaluator(momenta):
    @lru_cache(None)
    def jet(a):
        out = {}
        for s, k in enumerate(momenta):
            c = Q(1)
            for i, n in enumerate(a):
                c *= k[i]**n
            if c:
                out[UNIT[s]] = c
        return out

    @lru_cache(None)
    def monomial(m):
        return multiply(*(jet(a) for a in m))

    phi = jet(ZERO)
    first = [jet(a) for a in UNIT]
    kinetic = add(*(scale(ETA[i], multiply(first[i], first[i])) for i in range(4)))
    a_terms, b_terms = [], []
    for i in range(4):
        for j in range(4):
            hessian = jet(shift(UNIT[i], j))
            a_terms.append(scale(ETA[i]*ETA[j], multiply(hessian, hessian)))
            b_terms.append(scale(ETA[i]*ETA[j], multiply(hessian, first[i], first[j])))
    contractions = [multiply(phi, phi, add(*a_terms)),
                    multiply(phi, add(*b_terms)), multiply(kinetic, kinetic)]
    return jet, monomial, contractions, multiply(phi, phi, first[0], first[0])


def validate(momenta):
    assert all(dot(k, k) == 0 for k in momenta)
    assert all(sum(k[i] for k in momenta) == 0 for i in range(4))
    jet, monomial, contractions, anisotropic = evaluator(momenta)
    a, b, c = map(coefficient, contractions)
    pairings = (dot(momenta[0], momenta[1])*dot(momenta[2], momenta[3]) +
                dot(momenta[0], momenta[2])*dot(momenta[1], momenta[3]) +
                dot(momenta[0], momenta[3])*dot(momenta[1], momenta[2]))
    assert a == c == -2*b == 8*pairings and c != 0
    # 2105.12742v3 (3.28)-(3.29), literal coordinate-density normalization.
    normalized = (a/4, b/2, c/8)
    assert normalized == paper_polynomials(momenta)
    assert normalized[0]-2*normalized[1]+6*normalized[2] == Q(3, 2)*c
    divergence_checks = eom_checks = 0
    for d in range(4):
        for m in monomials(4, d):
            for i in range(4):
                actual = add(*(monomial(tuple(sorted(m[:j]+(shift(a, i),)+m[j+1:])))
                               for j, a in enumerate(m)))
                assert coefficient(actual) == 0
                divergence_checks += 1
    for d in range(3):
        for alpha in compositions(d, 4):
            wave = add(*(scale(ETA[i], jet(shift(alpha, i, 2))) for i in range(4)))
            assert wave == {}
            for r in range(3-d):
                for m in monomials(3, r):
                    assert coefficient(multiply(monomial(m), wave)) == 0
                    eom_checks += 1
    return dict(witness=str(c), normalized=[str(x) for x in normalized],
                anisotropic=str(coefficient(anisotropic)),
                divergence_checks=divergence_checks, eom_product_checks=eom_checks)


def main():
    cases = []
    permutation_checks = scaling_checks = 0
    for sine, cosine in [(Q(1), Q(0)), (Q(3, 5), Q(4, 5)),
                         (Q(5, 13), Q(12, 13)), (Q(0), Q(1)),
                         (Q(0), Q(-1)), (Q(-1), Q(0))]:
        k = ((Q(1), Q(0), Q(0), Q(1)), (Q(1), Q(0), Q(0), Q(-1)),
             (Q(-1), -sine, Q(0), -cosine), (Q(-1), sine, Q(0), cosine))
        result = validate(k)
        expected = Q(48)+16*cosine**2
        assert Q(result['witness']) == expected
        for permuted in permutations(k):
            assert coefficient(evaluator(permuted)[2][2]) == expected
            permutation_checks += 1
        for c in [Q(-2), Q(1, 3)]:
            scaled = tuple(tuple(c*x for x in row) for row in k)
            assert coefficient(evaluator(scaled)[2][2]) == c**4*expected
            scaling_checks += 1
        cases.append(result)

    k = ((1, 0, 0, 1), (1, 0, 0, -1), (-1, -1, 0, 0), (-1, 1, 0, 0))
    jet, _, _, anisotropic = evaluator(k)
    assert coefficient(anisotropic) == -8  # actual class survives, invariant coefficients vanish
    assert coefficient(multiply(*(jet(UNIT[0]) for _ in range(4)))) == 24
    changed = tuple(tuple(row) for row in k)
    time_after = [Q(3, 2)*p[0]-p[1]-Q(1, 2)*p[3] for p in changed]
    assert 24*time_after[0]*time_after[1]*time_after[2]*time_after[3] == 60
    nonconserving = tuple(tuple(-v for v in p) if i == 0 else p for i, p in enumerate(k))
    assert all(dot(p, p) == 0 for p in nonconserving)
    _, m, _, _ = evaluator(nonconserving)
    divergence = add(*(m(tuple(sorted((UNIT[0], ZERO, ZERO, ZERO)))) for _ in range(4)))
    assert coefficient(divergence) == -48
    nonnull = ((2, 0, 0, 1), (0, 0, 0, -1), k[2], k[3])
    assert all(sum(p[i] for p in nonnull) == 0 for i in range(4))
    j, m, _, _ = evaluator(nonnull)
    wave = add(*(scale(ETA[i], j(shift(ZERO, i, 2))) for i in range(4)))
    assert coefficient(multiply(m((ZERO, ZERO, ZERO)), wave)) == 12
    for inputs in [nonconserving, nonnull]:
        a, b, c = map(coefficient, evaluator(inputs)[2])
        assert (a/4, b/2, c/8) == paper_polynomials(inputs)
    assert [len(monomials(4, d)) for d in range(5)] == [1, 4, 20, 80, 305]
    print(json.dumps(dict(role='independent exact polynomial diagnostic; not a Lean premise',
                         cases=cases, permutations=permutation_checks, scalings=scaling_checks,
                         literal_paper_polynomial_checks=8,
                         negative_controls=dict(nonconserving_divergence=-48,
                                                nonnull_eom_product=12,
                                                noninvariant_before_after=[24, 60])), indent=2))


if __name__ == '__main__':
    main()
