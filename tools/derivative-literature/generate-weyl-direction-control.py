#!/usr/bin/env python3
"""Generate sparse Weyl/dual-vector upper certificates from actual group rows.

Gaussian rational elimination only proposes identities. Every emitted row and
component identity is checked by Lean against the actual SL(2,C) action.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
from pathlib import Path


@dataclass(frozen=True)
class G:
    re: Q = Q(0)
    im: Q = Q(0)

    def __add__(self, other):
        other = g(other)
        return G(self.re + other.re, self.im + other.im)

    __radd__ = __add__

    def __neg__(self):
        return G(-self.re, -self.im)

    def __sub__(self, other):
        return self + -g(other)

    def __mul__(self, other):
        other = g(other)
        return G(self.re*other.re-self.im*other.im,
                 self.re*other.im+self.im*other.re)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = g(other)
        norm = other.re**2 + other.im**2
        return self * G(other.re/norm, -other.im/norm)

    def __bool__(self):
        return bool(self.re or self.im)

    def conj(self):
        return G(self.re, -self.im)


def g(x):
    return x if isinstance(x, G) else G(Q(x))


ZERO, ONE, IM = G(), G(Q(1)), G(Q(0), Q(1))
Z = [1, -1, -1, 1]
X = [1, 1, -1, -1]
REAL = [[Q(3, 2), -1, 0, Q(-1, 2)], [-1, 1, 0, 1],
        [0, 0, 1, 0], [Q(1, 2), -1, 0, Q(1, 2)]]
IMAG = [[Q(3, 2), 0, 1, Q(-1, 2)], [0, 1, 0, 0],
        [1, 0, 1, -1], [Q(1, 2), 0, 1, Q(1, 2)]]
SPIN = [[[IM, ZERO], [ZERO, -IM]], [[ZERO, IM], [IM, ZERO]],
        [[ONE, ZERO], [ONE, ONE]], [[ONE, ZERO], [IM, ONE]]]
DIR = [[[Z[i] if i == j else 0 for j in range(4)] for i in range(4)],
       [[X[i] if i == j else 0 for j in range(4)] for i in range(4)], REAL, IMAG]
VARIABLES = list(product(range(2), range(2), range(4)))


def add(row, key, value):
    value = row.get(key, ZERO) + value
    if value:
        row[key] = value
    else:
        row.pop(key, None)


def scalar(x):
    x = g(x)
    def q(v):
        return f'({v.numerator}/{v.denominator} : ℂ)'
    if not x.im:
        return q(x.re)
    return f'({q(x.re)} + {q(x.im)}*Complex.I)'


def name(t):
    return ''.join(map(str, t))


def comp(t):
    return 'component f ' + ' '.join(map(str, t))


def expression(row):
    return ' + '.join(f'{scalar(v)}*{comp(t)}' for t, v in sorted(row.items())) or '0'


def certificates(c, d):
    free = [(0, 0, 0)] if c != d else []
    order = [t for t in VARIABLES if t not in free] + free
    raw = []
    for s, t in product(range(4), VARIABLES):
        a, b, i = t
        r = {}
        for u, v, j in VARIABLES:
            x, y = SPIN[s][a][u], SPIN[s][b][v]
            if c:
                x = x.conj()
            if d:
                y = y.conj()
            add(r, (u, v, j), x*y*DIR[s][i][j])
        add(r, t, -ONE)
        if r:
            raw.append((s, t, r))
    raw.sort(key=lambda r: (len(r[2]), r[0], r[1]))
    # norm_num cancels a lone nonzero imaginary coefficient in an equation to zero.
    # Lean checks the resulting rescaling, as it checks every other emitted identity.
    scales = {(s, t): next(iter(row.values()))
              if len(row) == 1 and not next(iter(row.values())).re else ONE
              for s, t, row in raw}
    pivots, records = {}, []
    for s, t, initial in raw:
        row, uses = dict(initial), []
        while row:
            p = next(k for k in order if k in row)
            if p not in pivots:
                factor = row[p]
                row = {k: v/factor for k, v in row.items()}
                pivots[p] = len(records)
                records.append((p, s, t, uses, factor, row))
                break
            index = pivots[p]
            v = row[p]
            uses.append((index, v))
            for k, w in records[index][-1].items():
                add(row, k, -v*w)
    assert len(records) == 16-len(free)
    assert not any(t in pivots for t in free)
    return records, order, free, scales


def generate(c, d):
    records, order, free, scales = certificates(c, d)
    label = ('R' if c else 'L') + ('R' if d else 'L')
    cb, db = str(c).lower(), str(d).lower()
    out = ['import Physics.FieldTheory.Jets.WeylDirectionInvariant.Core.Basic', '',
           '/-! Generated sparse certificates, checked against actual group rows. -/',
           f'namespace Physics.WeylDirectionInvariant.{label}', 'set_option autoImplicit false',
           'noncomputable section', 'open Math LorentzDirections LorentzFiniteControls',
           'variable (f : Tensor)',
           f'  (h : ∀ g u v w, f (LorentzJetIBP.weyl {cb} g u)',
           f'    (LorentzJetIBP.weyl {db} g v) (direction g w) = f u v w)', '']
    normalizer = '(norm := ring_nf)'
    for n, (p, s, t, uses, factor, row) in enumerate(records):
        out += ['include h in', f'theorem row{n} : {expression(row)} = 0 := by',
                f'  have he := row {cb} {db} f h {s} ' + ' '.join(map(str, t)),
                '  norm_num [Fin.sum_univ_succ,spinRows,sample,WeylCurrentCovariance.component,',
                '    flipZ,flipX,shear,directionRows,signsZ,signsX,realRows,imagRows] at he',
                f'  linear_combination {normalizer} ' + scalar(scales[s, t]/factor) + '*he' + ''.join(
                    f' - {scalar(v/factor)}*(row{i} f h)' for i, v in uses), '']
    values = {t: {t: ONE} for t in free}
    for n in sorted(range(len(records)), key=lambda n: order.index(records[n][0]), reverse=True):
        p, _, _, _, _, row = records[n]
        val = {}
        for k, v in row.items():
            if k != p:
                for t, w in values[k].items():
                    add(val, t, -v*w)
        values[p] = val
        out += ['include h in', f'theorem value{name(p)} : {comp(p)} = {expression(val)} := by',
                f'  have he := row{n} f h']
        deps = [k for k in row if k != p and k not in free]
        if deps:
            out += ['  rw [' + ','.join(f'value{name(k)} f h' for k in deps) + '] at he']
        out += [f'  linear_combination {normalizer} he', '']
    rhs = '0' if c == d else 'component f 0 0 0 * kernel ' + ('b a i' if c else 'a b i')
    out += ['include h in', f'theorem components (a b : Fin 2) (i : Fin 4) :',
            f'    component f a b i = {rhs} := by',
            '  fin_cases a <;> fin_cases b <;> fin_cases i',
            '  all_goals norm_num [kernel,fromPauli,' + ','.join(
                f'value{name(t)} f h' for t in values if t not in free) + ']',
            ]
    if c != d:
        out += ['  all_goals ring']
    out += ['', 'end', f'end Physics.WeylDirectionInvariant.{label}', '']
    return label, '\n'.join(out), len(records)


def main():
    target = Path('Physics/FieldTheory/Jets/WeylDirectionInvariant/Core')
    for c, d in product([False, True], repeat=2):
        label, source, rank = generate(c, d)
        (target / f'{label}.lean').write_text(source)
        print(f'{label}: {rank} necessary-row pivots; Lean verification required')


if __name__ == '__main__':
    main()
