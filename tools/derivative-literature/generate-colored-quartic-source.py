#!/usr/bin/env python3
"""Generate complete colored four-field/order-four source coverage.

All 35 allocations and each field permutation are verified by Lean. The
existing uncolored partition generator supplies only arithmetic proof text.
Run from the repository root; no generated list is a theorem premise.
"""
from itertools import product
from pathlib import Path
import runpy


def generate():
    old = runpy.run_path('tools/derivative-literature/generate-quartic-source.py')
    partitions = old['generate']().split('theorem product_mem')[0]
    out = ['import Math.Algebra.Constructions.ColoredQuarticWords',
           'import Math.Algebra.Constructions.ColoredDegreeFour', '',
           '/-! Entire colored grade coverage, before equations or invariance. -/',
           'namespace Math.ColoredQuarticSource', 'set_option autoImplicit false',
           'noncomputable section', 'open ScalarJetAlgebra MvPolynomial ColoredQuarticWords',
           'variable {S : Type*}', 'abbrev J (S : Type*) := Index S (Fin 4)', '']
    out += ['theorem jet0 (j : J S) (hj : order j.2 = 0) :',
            '    (X j : A S) = field j.1 := by',
            '  rcases j with ⟨s,a⟩', '  change order a = 0 at hj',
            '  rw [ScalarDegreeTwo.order_zero hj]', '  rfl', '']
    for n in range(1, 5):
        args = ['i', 'k', 'l', 'm'][:n]
        order = f'ScalarDegreeTwo.order_{["", "one", "two"][n]}' if n < 3 else \
            f'ScalarDegreeFour.order_{"three" if n == 3 else "four"}'
        out += [f'theorem jet{n} (j : J S) (hj : order j.2 = {n}) :',
                '    ∃ ' + ' '.join(args) + ' : Fin 4, (X j : A S) = ' +
                f'j{n} j.1 ' + ' '.join(f'(E {a})' for a in args) + ' := by',
                '  rcases j with ⟨s,a⟩', f'  change order a = {n} at hj',
                '  obtain ⟨' + ','.join(args + ['he']) + f'⟩ := {order} hj',
                '  refine ⟨' + ','.join(args + ['?_']) + '⟩',
                '  simp [' + ','.join([f'j{k}' for k in range(n, 0, -1)] +
                    ['E', 'he', 'field', 'D', 'ScalarJetAlgebra.shift',
                     'add_comm'] + (['add_left_comm'] if n >= 3 else [])) + ']', '']
    out += ['def words (S : Type*) : Set (A S) :=',
            '  {p | ∃ a : Fin 4 → S, ∃ r : Fin 5, ∃ i j k l : Fin 4,',
            '    p = word a r (E i) (E j) (E k) (E l)}',
            'def wordSpan (S : Type*) : Submodule ℂ (A S) := Submodule.span ℂ (words S)',
            'theorem word_mem (a : Fin 4 → S) (r : Fin 5) (i j k l : Fin 4) :',
            '    word a r (E i) (E j) (E k) (E l) ∈ wordSpan S :=',
            '  Submodule.subset_span ⟨a,r,i,j,k,l,rfl⟩', '', partitions]
    allocations = [t for t in product(range(5), repeat=4) if sum(t) == 4]
    def tree(xs):
        if len(xs) == 1:
            return xs[0]
        mid = len(xs)//2
        return '(' + tree(xs[:mid]) + ' | ' + tree(xs[mid:]) + ')'
    for case, t in enumerate(allocations):
        out += [f'private theorem allocation{case} (j k l m : J S)',
                '    ' + ' '.join(f'(h{v} : order {v}.2 = {n})' for v, n in zip('jklm', t)) + ' :',
                '    (X j*X k*X l*X m : A S) ∈ wordSpan S := by']
        data = []
        for v, n in zip('jklm', t):
            args = [f'a_{v}{i}' for i in range(n)]
            data.append((v, n, args))
            if n:
                out.append('  obtain ⟨' + ','.join(args + [f'e{v}']) +
                           f'⟩ := jet{n} {v} h{v}')
            else:
                out.append(f'  have e{v} := jet0 {v} h{v}')
        ordered = [d for d in data if d[1] == 0] + sorted(
            [d for d in data if d[1]], key=lambda d: -d[1])
        labels = '![' + ','.join(f'{v}.1' for v, _, _ in ordered) + ']'
        args = [x for _, _, xs in ordered for x in xs]
        partition = sorted([n for n in t if n], reverse=True)
        r = [[4], [3,1], [2,2], [2,1,1], [1,1,1,1]].index(partition)
        term = f'word {labels} {r} ' + ' '.join(f'(E {v})' for v in args)
        expr = '*'.join(f'(field {v}.1)' if not n else
                        f'(j{n} {v}.1 ' + ' '.join(f'(E {x})' for x in xs) + ')'
                        for v, n, xs in data)
        rhs = '*'.join(f'(field {v}.1)' if not n else
                       f'(j{n} {v}.1 ' + ' '.join(f'(E {x})' for x in xs) + ')'
                       for v, n, xs in ordered)
        out += ['  rw [ej,ek,el,em]', f'  have he : {expr} = {term} := by',
                f'    change {expr} = {rhs}', '    ring',
                '  rw [he]', f'  exact word_mem {labels} {r} ' + ' '.join(args), '']
    out += ['theorem product_mem (j k l m : J S)',
            '    (hd : order j.2+order k.2+order l.2+order m.2 = 4) :',
            '    (X j*X k*X l*X m : A S) ∈ wordSpan S := by',
            '  rcases partitions _ _ _ _ hd with ' + tree(['h']*35)]
    for case, _ in enumerate(allocations):
        out += ['  · obtain ⟨hj,hk,hl,hm⟩ := h',
                f'    exact allocation{case} j k l m hj hk hl hm']
    out += ['', 'theorem grade_eq_span : V S = wordSpan S := by',
            '  apply le_antisymm', '  · intro p hp', '    rw [p.as_sum]',
            '    apply Submodule.sum_mem', '    intro a ha',
            '    have hw := hp (MvPolynomial.mem_support_iff.mp ha)',
            '    obtain ⟨j,k,l,m,he,hd⟩ := ColoredDegreeFour.monomial_four hw',
            '    have hc : (monomial a (p.coeff a) : A S) = p.coeff a • monomial a 1 := by',
            '      simp [smul_monomial]', '    rw [hc,he]',
            '    exact (wordSpan S).smul_mem _ (product_mem j k l m hd)',
            '  · apply Submodule.span_le.mpr', '    rintro p ⟨a,r,i,j,k,l,rfl⟩',
            '    exact word_grade a r (E i) (E j) (E k) (E l)', '', 'end',
            'end Math.ColoredQuarticSource', '']
    return '\n'.join(out)


if __name__ == '__main__':
    Path('Math/Algebra/Constructions/ColoredQuarticSource.lean').write_text(generate())
    print('Generated 35 allocations with independent field labels; Lean verification required.')
