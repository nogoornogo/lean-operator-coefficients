#!/usr/bin/env python3
"""Exact real-rational Hermitian one-N matching through external degree six.

All 36 external Grassmann generators and four independent heavy generators
are retained. H.c. reverses products and swaps fields. Heavy left derivatives
are computed from the action, not supplied solutions. Higher external degrees
are discarded explicitly; they cannot contribute to the selected degree-six
coefficient. Standard library only; diagnostic, never a Lean premise.
"""
from fractions import Fraction as Q
from itertools import product
import runpy
from pathlib import Path

base = runpy.run_path(str(Path(__file__).with_name('check-tree-level.py')))
add, scale, parity, eps = (base[k] for k in ('add', 'scale', 'parity', 'eps'))


def mul(p, q, limit=6):
    out = {}
    for a, ca in p.items():
        for b, cb in q.items():
            if len(a) + len(b) > limit or set(a).intersection(b):
                continue
            word = a+b
            key = tuple(sorted(word))
            out[key] = out.get(key, 0) + parity(word)*ca*cb
    return {m: c for m, c in out.items() if c}


def gen(i):
    return {(i,): Q(1)}


def hc(p):
    def swap(i):
        return i+18 if i < 18 else i-18 if i < 36 else i+2 if i < 38 else i-2
    out = {}
    for word, c in p.items():
        rev = tuple(swap(i) for i in reversed(word))
        key = tuple(sorted(rev))
        out[key] = out.get(key, 0) + parity(rev)*c
    return {m: c for m, c in out.items() if c}


def derivative(p, i):
    out = {}
    for word, c in p.items():
        if i in word:
            k = word.index(i)
            out[word[:k]+word[k+1:]] = (-1)**k*c
    return out


def substitute(p, n, limit=6):
    out = {}
    for word, c in p.items():
        term = {(): c}
        for i in word:
            term = mul(term, n[i-36] if i >= 36 else gen(i), limit)
        out = add(out, term)
    return out


def degree(p, d):
    return {w: c for w, c in p.items() if len(w) == d}


def holomorphic(p):
    return {w: c for w, c in p.items() if all(i < 18 for i in w)}


u, down, current, printed = (base[k] for k in ('u', 'down', 'current', 'printed'))
heavy = [gen(i) for i in range(36, 40)]
vertices = [add(mul(heavy[0], u[c][1]), scale(-1, mul(heavy[1], u[c][0])))
            for c in range(3)]
for m, mass, a, b in [(Q(2), Q(3), Q(1), Q(1)), (Q(-5), Q(7), Q(2), Q(-6))]:
    mass_term = scale(-mass, mul(heavy[0], heavy[1]))
    interaction = add(*(scale(-1/m, mul(
        add(scale(a, U), scale(b, hc(D))),
        add(scale(b, D), scale(a, hc(U)))))
        for U, D in zip(vertices, down)))
    action = add(mass_term, hc(mass_term), interaction)
    assert hc(action) == action
    ds = [derivative(interaction, i) for i in range(36, 40)]
    n = [{}, {}, {}, {}]
    # Each iteration raises new terms by two external degrees. Two suffice
    # for degrees three and five; the third is a fixed-point control.
    def step(n):
        f = [substitute(p, n, 5) for p in ds]
        return [scale(-1/mass, f[1]), scale(1/mass, f[0]),
                scale(1/mass, f[3]), scale(-1/mass, f[2])]
    n = step(step(n))
    assert step(n) == n
    assert hc(n[0]) == n[2] and hc(n[1]) == n[3]
    for i in range(36, 40):
        assert substitute(derivative(action, i), n, 5) == {}
    effective = substitute(action, n)
    assert hc(effective) == effective
    g = a*b/m
    chiral6 = scale(g*g/mass, mul(current[0], current[1]))
    mixed4 = scale(-b*b/m, add(*(mul(hc(D), D) for D in down)))
    assert degree(effective, 4) == mixed4
    assert degree(effective, 6) == add(chiral6, hc(chiral6))
    assert holomorphic(effective) == chiral6
    assert holomorphic(n[2]) == {} and holomorphic(n[3]) == {}
    assert holomorphic(n[0]) == scale(-g/mass, current[0])
    assert holomorphic(n[1]) == scale(-g/mass, current[1])
    assert chiral6 == scale((a*b)**2/(2*m*m*mass), printed)
    # Check original scalar action, including literal H.c., at its solution.
    full = add(mass_term, hc(mass_term))
    for U, D in zip(vertices, down):
        U0 = substitute(U, n)
        J = add(scale(a, U0), scale(b, hc(D)))
        x, y = scale(-1/m, J), scale(-1/m, hc(J))
        assert y == hc(x)
        v = add(scale(a, mul(U0, y)), scale(b, mul(x, D)))
        full = add(full, scale(m, mul(x, y)), v, hc(v))
    assert substitute(full, n) == effective
    print('Hermitian case:', (m, mass, a, b), 'degree-4 terms:', len(mixed4),
          'degree-6 terms:', len(degree(effective, 6)),
          'stationary residual through degree 5: zero')
print('Full H.c. action diagnostic passed: holomorphic degree-six coefficient unchanged; '
      'mixed degree-four terms retained; higher-degree matching not asserted.')
