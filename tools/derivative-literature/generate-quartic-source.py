#!/usr/bin/env python3
"""Generate all 35 derivative allocations at field count four/order four.

Every generated source coverage claim is proved in Lean, using the actual
weighted support and the explicit jet identities. No enumerated list is a
theorem premise. Run from the repository root.
"""
from itertools import product
from pathlib import Path


def generate():
    allocations = [t for t in product(range(5), repeat=4) if sum(t) == 4]
    assert len(allocations) == 35
    clauses = [' ∧ '.join(f'{v} = {n}' for v, n in zip('abcd', t)) for t in allocations]
    def tree(xs, operator):
        if len(xs) == 1:
            return xs[0]
        mid = len(xs)//2
        return '(' + tree(xs[:mid], operator) + operator + tree(xs[mid:], operator) + ')'
    def inject(index, size, proof):
        if size == 1:
            return proof
        mid = size//2
        if index < mid:
            return 'Or.inl (' + inject(index, mid, proof) + ')'
        return 'Or.inr (' + inject(index-mid, size-mid, proof) + ')'
    out = []
    for a in range(5):
        small = ['(' + ' ∧ '.join(f'{v} = {n}' for v, n in zip('bcd', t[1:])) + ')'
                 for t in allocations if t[0] == a]
        out += [f'private theorem partitions{a} (b c d : ℕ) (h : {a}+b+c+d = 4) :',
                '    ' + tree(small, ' ∨ ') + ' := by',
                f'  have hb : b ≤ {4-a} := by omega', '  interval_cases b']
        local = [t for t in allocations if t[0] == a]
        for b in range(5-a):
            out += [f'  · have hc : c ≤ {4-a-b} := by omega', '    interval_cases c']
            for c in range(5-a-b):
                index = local.index((a,b,c,4-a-b-c))
                out.append('    · exact ' + inject(index,len(local),'⟨rfl,rfl,by omega⟩'))
        out.append('')
    out += ['theorem partitions (a b c d : ℕ) (h : a+b+c+d = 4) :',
            '    ' + tree(['(' + c + ')' for c in clauses], ' ∨ ') + ' := by',
            '  have ha : a ≤ 4 := by omega', '  interval_cases a']
    for a in range(5):
        subset = [(i, t) for i, t in enumerate(allocations) if t[0] == a]
        out.append(f'  · have he := partitions{a} b c d h')
        if len(subset) > 1:
            out.append('    rcases he with ' + tree(['he' for _ in subset], ' | '))
        for i, t in subset:
            out.append(('    · ' if len(subset) > 1 else '    ') + 'exact ' + inject(i,35,'⟨rfl,he⟩'))
    out += ['',
           'theorem product_mem (j k l m : J)',
           '    (hd : ScalarJetAlgebra.order j.2+ScalarJetAlgebra.order k.2+',
           '      ScalarJetAlgebra.order l.2+ScalarJetAlgebra.order m.2 = 4) :',
           '    (X j*X k*X l*X m : OffShell) ∈ wordSpan := by',
           '  rcases partitions _ _ _ _ hd with ' + tree(['h' for _ in allocations], ' | ')]
    for t in allocations:
        out += ['  · obtain ⟨hj,hk,hl,hm⟩ := h']
        coords = []
        for v, n in zip('jklm', t):
            if n == 0:
                out.append(f'    have e{v} := jet0 {v} h{v}')
            else:
                args = ['a_' + v + str(i) for i in range(n)]
                coords.append((n, args))
                out.append(f'    obtain ⟨' + ','.join(args + [f'e{v}']) + f'⟩ := jet{n} {v} h{v}')
        out += ['    rw [ej,ek,el,em]']
        coords.sort(key=lambda a: -a[0])
        partition = sorted((n for n in t if n), reverse=True)
        r = [[4], [3,1], [2,2], [2,1,1], [1,1,1,1]].index(partition)
        args = [x for _, xs in coords for x in xs]
        term = f'word {r} ' + ' '.join(f'(E {v})' for v in args)
        expr = '*'.join('(field)' if n == 0 else '(' + f'j{n} ' + ' '.join(f'(E a_{v}{i})' for i in range(n)) + ')'
                        for v, n in zip('jklm', t))
        js = lambda n, xs: f'j{n} ' + ' '.join(f'(E {x})' for x in xs)
        rhs = [f'field^3*({js(4,args)})',
               f'field^2*({js(3,args[:3])})*({js(1,args[3:])})',
               f'field^2*({js(2,args[:2])})*({js(2,args[2:])})',
               f'field*({js(2,args[:2])})*({js(1,args[2:3])})*({js(1,args[3:])})',
               '*'.join(f'({js(1,[x])})' for x in args)][r]
        out += [f'    have he : {expr} = {term} := by',
                f'      change {expr} = {rhs}', '      ring',
                '    rw [he]', f'    exact word_mem {r} ' + ' '.join(args)]
    out += ['', 'theorem grade_eq_span : V = wordSpan := by',
            '  apply le_antisymm', '  · intro p hp', '    rw [p.as_sum]',
            '    apply Submodule.sum_mem', '    intro a ha',
            '    have hw := hp (MvPolynomial.mem_support_iff.mp ha)',
            '    obtain ⟨j,k,l,m,he,hd⟩ := ScalarDegreeFour.monomial_four hw',
            '    have hc : (monomial a (p.coeff a) : OffShell) = p.coeff a • monomial a 1 := by simp [smul_monomial]',
            '    rw [hc,he]', '    exact wordSpan.smul_mem _ (product_mem j k l m hd)',
            '  · apply Submodule.span_le.mpr', '    rintro p ⟨r,i,j,k,l,rfl⟩',
            '    exact word_grade r (E i) (E j) (E k) (E l)', '']
    return '\n'.join(out)


if __name__ == '__main__':
    path = Path('Physics/FieldTheory/Jets/Scalar/QuarticFour/ScalarQuarticFourSource.lean')
    prefix = path.read_text().split('/- Generated source coverage follows. -/')[0]
    path.write_text(prefix + '/- Generated source coverage follows. -/\n\n' + generate() +
                    '\nend\nend Physics.ScalarQuarticFourSource\n')
    print('Generated all 35 source allocations for Lean verification.')
