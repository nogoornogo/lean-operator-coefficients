#!/usr/bin/env python3
"""Propose bounded first-jet Higgs rows, rechecked against actual group actions."""
from fractions import Fraction as Q
from itertools import product, combinations_with_replacement
from pathlib import Path
from math import prod

WEIGHT = [4, 2, -4, -2]
ROT = [[Q(3, 5), Q(-4, 5), 0, 0], [Q(4, 5), Q(3, 5), 0, 0],
       [0, 0, Q(3, 5), Q(-4, 5)], [0, 0, Q(4, 5), Q(3, 5)]]
RAW = [(i, *t) for i in range(4) for t in combinations_with_replacement(range(4), 3)]
VARS = [t for t in RAW if sum(WEIGHT[i] for i in t) == 0]
FREE = [(0, 0, 2, 2), (2, 0, 0, 2)]
ORDER = [t for t in VARS if t not in FREE] + FREE


def add(r, k, v):
    r[k] = r.get(k, Q(0)) + v
    if not r[k]:
        del r[k]


def scalar(q):
    q = Q(q)
    return f'({q.numerator}/{q.denominator} : ℂ)'


def name(t):
    return ''.join(map(str, t))


def comp(t):
    return 'K f ' + ' '.join(map(str, t))


def expression(r):
    return ' + '.join(f'{scalar(v)}*{comp(t)}' for t, v in sorted(r.items())) or '0'


def records():
    raw = []
    for t in RAW:
        r = {}
        for v in product(range(4), repeat=4):
            if sum(WEIGHT[i] for i in v) == 0:
                add(r, (v[0], *sorted(v[1:])), prod(Q(ROT[a][b]) for a, b in zip(t, v)))
        if t in VARS:
            add(r, t, -1)
        if r:
            raw.append((t, r))
    raw.sort(key=lambda r: (len(r[1]), r[0]))
    piv, ans = {}, []
    for t, initial in raw:
        r, uses = dict(initial), []
        while r:
            p = next(k for k in ORDER if k in r)
            if p not in piv:
                factor = r[p]
                r = {k: v/factor for k, v in r.items()}
                piv[p] = len(ans)
                ans.append((p, t, factor, uses, r))
                break
            n = piv[p]
            value = r[p]
            uses.append((n, value))
            for k, v in ans[n][-1].items():
                add(r, k, -value*v)
    assert len(RAW) == 80 and len(VARS) == 8 and len(ans) == 6
    assert not any(t in piv for t in FREE)
    return ans


HEADER = ('\n/-! Generated sparse certificates; Lean checks every actual-group identity. -/\n'
          'namespace Physics.HiggsFirstInternal\nset_option autoImplicit false\n'
          'noncomputable section\nopen Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls\n'
          'attribute [local simp] mul_add add_mul sub_mul mul_sub smul_mul_assoc mul_smul_comm smul_smul smul_eq_mul\n'
          'variable (f : A →ₗ[ℂ] ℂ)\n'
          '  (hI : ∀ g i j k l, f (T g (mono i j k l)) = f (mono i j k l))\n\n')


def generate():
    rows = records()
    out = ['import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Basic', HEADER]
    for n, (p, t, factor, uses, r) in enumerate(rows):
        out += ['include hI in', f'theorem row{n} : {expression(r)} = 0 := by',
                f'  have he := rotation_value f hI ' + ' '.join(map(str, t)),
                '  norm_num [HiggsQuarticFourInternalUpper.rotateField] at he',
                '  simp only [← K_apply,normal_form f hI] at he',
                '  norm_num [normalK,ordered,weight] at he',
                '  linear_combination ' + scalar(1/factor) + '*he' + ''.join(
                    f' - {scalar(v/factor)}*(row{i} f hI)' for i, v in uses), '']
    values = {t: {t: Q(1)} for t in FREE}
    for n in sorted(range(len(rows)), key=lambda n: ORDER.index(rows[n][0]), reverse=True):
        p, _, _, _, r = rows[n]
        value = {}
        for k, v in r.items():
            if k != p:
                for t, w in values[k].items():
                    add(value, t, -v*w)
        values[p] = value
        out += ['include hI in', f'theorem value{name(p)} : {comp(p)} = {expression(value)} := by',
                f'  have he := row{n} f hI']
        deps = [k for k in r if k != p and k not in FREE]
        if deps:
            out += ['  rw [' + ','.join(f'value{name(k)} f hI' for k in deps) + '] at he']
        out += ['  linear_combination he', '']
    out += ['end', 'end Physics.HiggsFirstInternal', '']
    target = Path('Physics/FieldTheory/Jets/HiggsFirstInternal/Core')
    write(target / 'Rows.lean', '\n'.join(out))
    for i in range(4):
        h0, h2 = ('h0', '_h2') if i < 2 else ('_h0', 'h2')
        source = ['import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Rows', HEADER,
                  'include hI in', f'theorem zero{i} ({h0} : K f 0 0 2 2 = 0) ({h2} : K f 2 0 0 2 = 0)',
                  f'    (j k l : Fin 4) : K f {i} j k l = 0 := by',
                  '  fin_cases j <;> fin_cases k <;> fin_cases l']
        for j, k, l in product(range(4), repeat=3):
            t = (i, j, k, l)
            if sum(WEIGHT[a] for a in t) != 0:
                source += [f'  · exact vanish f hI {i} {j} {k} {l} (by decide +kernel)']
            else:
                canonical = (i, *sorted((j, k, l)))
                source += [f'  · change K f {i} {j} {k} {l} = 0',
                           f'    rw [normalize f {i} {j} {k} {l}]',
                           '    norm_num [ordered,' + ','.join(
                               f'value{name(t)} f hI' for t in values if t not in FREE) + f',{h0},{h2}]']
                assert canonical in values
        source += ['', 'end', 'end Physics.HiggsFirstInternal', '']
        write(target / f'Zero{i}.lean', '\n'.join(source))


def write(path, source):
    if not path.exists() or path.read_text() != source:
        path.write_text(source)


if __name__ == '__main__':
    generate()
    print('80 marked monomials, 8 phase-zero coordinates, 6 proposed row pivots; Lean verification required')
