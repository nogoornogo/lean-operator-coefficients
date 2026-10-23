#!/usr/bin/env python3
"""Ordered colored-wave moment candidates, checked by Lean kernel reduction.

Unlike the scalar cubature, wave labels are never permuted when identifying
configurations. The finite construction supplies data, not an invariance premise.
"""
from collections import deque, Counter
from itertools import combinations_with_replacement
from pathlib import Path


def generate():
    identity = tuple(tuple(2*int(i == j) for j in range(4)) for i in range(4))
    generators = [tuple(tuple(2*int(p[i] == j) for j in range(4)) for i in range(4))
                  for p in [(1,0,2,3),(0,2,1,3),(0,1,3,2)]]
    generators += [tuple(tuple((-2 if i == 0 else 2)*int(i == j) for j in range(4))
                         for i in range(4)),
                   tuple(tuple((-1)**((i & j).bit_count()) for j in range(4)) for i in range(4))]
    def mul(a, b):
        c = tuple(tuple(sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4))
                  for i in range(4))
        assert all(x % 2 == 0 for row in c for x in row)
        return tuple(tuple(x//2 for x in row) for row in c)
    queue, matrices = deque([identity]), {identity}
    while queue:
        a = queue.popleft()
        for b in generators:
            c = mul(a, b)
            if c not in matrices:
                matrices.add(c)
                queue.append(c)
    assert len(matrices) == 1152
    def phase(z, p):
        x, y = z
        return [(x,y),(-y,x),(-x,-y),(y,-x)][p]
    configs = []
    for cosine in [0, 1, -1]:
        sine = int(cosine == 0)
        base = [[(1,0),(0,0),(0,0),(0,1)],[(1,0),(0,0),(0,0),(0,-1)],
                [(-1,0),(0,-sine),(0,0),(0,-cosine)],
                [(-1,0),(0,sine),(0,0),(0,cosine)]]
        counts = Counter()
        for a in matrices:
            waves = []
            for b in base:
                e = [tuple(sum(a[i][j]*b[j][p] for j in range(4)) for p in range(2))
                     for i in range(4)]
                waves.append([e[0]]+[phase(z,3) for z in e[1:]])
            key = min(tuple(tuple(phase(z,p) for z in row) for row in waves) for p in range(4))
            counts[key] += 1
        assert len(set(counts.values())) == 1
        configs.append(sorted(counts))
    assert list(map(len, configs)) == [288,72,72]
    folder = Path('Math/Algebra/HiggsFourWaveCubature')
    folder.mkdir(exist_ok=True)
    def vector(xs):
        return '![' + ','.join(xs) + ']'
    text = '''import Math.Algebra.Waves.FourWavePolarization
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Ordered wave data; all conservation, nullness and moment claims require
kernel checking. No finite group order or generation assertion is a premise. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
def count : Fin 3 → ℕ := ![288,72,72]
'''
    for r, nodes in enumerate(configs):
        def binary(start, stop, indent):
            if stop-start == 1:
                return vector([vector([f'⟨{x},{y}⟩' for x,y in row]) for row in nodes[start]])
            mid = (start+stop)//2
            return f'if a.val < {mid} then\n' + indent + '  ' + binary(start, mid, indent+'  ') + \
                '\n' + indent + 'else\n' + indent + '  ' + binary(mid, stop, indent+'  ')
        text += f'def raw{r} (a : Fin {len(nodes)}) : Fin 4 → Fin 4 → GaussianInt :=\n  ' + \
            binary(0, len(nodes), '  ') + '\n'
    text += '\ndef raw (r : Fin 3) : Fin (count r) → Fin 4 → Fin 4 → GaussianInt := match r with\n'
    text += '  | 0 => raw0\n  | 1 => raw1\n  | 2 => raw2\n'
    text += '''
def metric (i j : Fin 4) : GaussianInt := if i = j then (if i = 0 then 1 else -1) else 0
def gram (r : Fin 3) : Fin 4 → Fin 4 → GaussianInt := ![
  ![![0,8,-4,-4],![8,0,-4,-4],![-4,-4,0,8],![-4,-4,8,0]],
  ![![0,8,0,-8],![8,0,-8,0],![0,-8,0,8],![-8,0,8,0]],
  ![![0,8,-8,0],![8,0,0,-8],![-8,0,0,8],![0,-8,8,0]]] r
def factor : Fin 3 → GaussianInt := ![4,1,1]
def expected (r : Fin 3) (s t u v i j k l : Fin 4) : GaussianInt :=
  factor r*((5*gram r s t*gram r u v-gram r s u*gram r t v-gram r s v*gram r t u)*metric i j*metric k l+
    (5*gram r s u*gram r t v-gram r s t*gram r u v-gram r s v*gram r t u)*metric i k*metric j l+
    (5*gram r s v*gram r t u-gram r s t*gram r u v-gram r s u*gram r t v)*metric i l*metric j k)
def sumMoment (r : Fin 3) (s t u v i j k l : Fin 4) : GaussianInt :=
  ∑ a : Fin (count r), raw r a s i*raw r a t j*raw r a u k*raw r a v l
theorem conservation (r : Fin 3) : ∀ a : Fin (count r), ∀ i : Fin 4,
    (∑ s : Fin 4, raw r a s i) = 0 := by
  fin_cases r <;> decide +kernel
theorem null (r : Fin 3) : ∀ a : Fin (count r), ∀ s : Fin 4,
    (raw r a s 0)^2-(raw r a s 1)^2-(raw r a s 2)^2-(raw r a s 3)^2 = 0 := by
  fin_cases r <;> decide +kernel
end Math.HiggsFourWaveCubature
'''
    (folder/'Basic.lean').write_text(text)
    flips = 'import Math.Algebra.HiggsFourWaveCubature.Basic\n\n'
    flips += '/-! Exact coordinate-sign reindexing data; checked in FlipChecks modules. -/\n'
    flips += 'namespace Math.HiggsFourWaveCubature\nset_option autoImplicit false\n'
    def binary_values(values, start, stop, indent):
        if stop-start == 1:
            return str(values[start])
        mid = (start+stop)//2
        return f'if a.val < {mid} then\n' + indent + '  ' + \
            binary_values(values, start, mid, indent+'  ') + '\n' + indent + 'else\n' + \
            indent+'  '+binary_values(values, mid, stop, indent+'  ')
    for r, nodes in enumerate(configs):
        lookup = {k:i for i,k in enumerate(nodes)}
        for axis in range(4):
            targets, phases = [], []
            for node in nodes:
                flipped = tuple(tuple((-x,-y) if j == axis else (x,y)
                                      for j,(x,y) in enumerate(row)) for row in node)
                candidates = [tuple(tuple(phase(z,p) for z in row) for row in flipped)
                              for p in range(4)]
                canonical = min(candidates)
                targets.append(lookup[canonical])
                phases.append(candidates.index(canonical))
            assert all(targets[targets[a]] == a for a in range(len(nodes)))
            for kind, values, size in [('flip',targets,len(nodes)),('phase',phases,4)]:
                flips += f'def {kind}{r}_{axis} (a : Fin {len(nodes)}) : Fin {size} :=\n  ' + \
                    binary_values(values, 0, len(nodes), '  ') + '\n'
    flips += '\ndef flipIndex (r : Fin 3) (i : Fin 4) : Fin (count r) → Fin (count r) := match r with\n'
    for r in range(3):
        flips += f'  | {r} => ![flip{r}_0,flip{r}_1,flip{r}_2,flip{r}_3] i\n'
    flips += '\ndef phaseIndex (r : Fin 3) (i : Fin 4) : Fin (count r) → Fin 4 := match r with\n'
    for r in range(3):
        flips += f'  | {r} => ![phase{r}_0,phase{r}_1,phase{r}_2,phase{r}_3] i\n'
    flips += '''
def root : Fin 4 → GaussianInt := ![1,⟨0,1⟩,-1,⟨0,-1⟩]
def flipPhase (r : Fin 3) (i : Fin 4) (a : Fin (count r)) := root (phaseIndex r i a)
def sign (i j : Fin 4) : GaussianInt := if i = j then -1 else 1
theorem phase_four (r : Fin 3) (i : Fin 4) (a : Fin (count r)) : (flipPhase r i a)^4 = 1 := by
  have hr : ∀ p : Fin 4, (root p)^4 = 1 := by decide +kernel
  exact hr _
end Math.HiggsFourWaveCubature
'''
    (folder/'FlipData.lean').write_text(flips)
    for r in range(3):
        checks = 'import Math.Algebra.HiggsFourWaveCubature.FlipData\n\n'
        checks += '/-! Kernel-checked coordinate-sign closure, including global phases. -/\n'
        checks += 'namespace Math.HiggsFourWaveCubature\nset_option autoImplicit false\n'
        checks += f'theorem flip_involutive{r} (i : Fin 4) : ∀ a : Fin (count {r}),\n'
        checks += f'    flipIndex {r} i (flipIndex {r} i a) = a := by\n  fin_cases i <;> decide +kernel\n'
        checks += f'theorem flip_value{r} (i : Fin 4) : ∀ a : Fin (count {r}), ∀ s j : Fin 4,\n'
        checks += f'    raw {r} (flipIndex {r} i a) s j = flipPhase {r} i a*sign i j*raw {r} a s j := by\n'
        checks += '  fin_cases i <;> decide +kernel\nend Math.HiggsFourWaveCubature\n'
        (folder/f'FlipChecks{r}.lean').write_text(checks)
    patterns = list(combinations_with_replacement(range(4), 4))
    for r in range(3):
        for m, slots in enumerate(patterns):
            dependency = ['Structural.TransverseMoments','Structural.CollinearMoments','Structural.SecondCollinear'][r]
            text = f'import Math.Algebra.HiggsFourWaveCubature.{dependency}\n\n'
            identity = ['transverse','collinear','second-collinear'][r]
            text += f'/-! Exact ordered moments, derived from the structural {identity} identity. -/\n'
            text += 'namespace Math.HiggsFourWaveCubature\nset_option autoImplicit false\n'
            args = ' '.join(map(str, slots))
            for i in range(4):
                text += f'\ntheorem moments{r}_{m}_{i} : ∀ j k l : Fin 4,\n'
                text += f'    sumMoment {r} {args} {i} j k l = expected {r} {args} {i} j k l := by\n'
                route = ['Structural.Transverse.transverse_moments','Structural.collinear_moments',
                         'Structural.SecondCollinear.second_collinear_moments'][r]
                text += f'  intro j k l\n  exact {route} {args} {i} j k l\n'
            text += '\nend Math.HiggsFourWaveCubature\n'
            (folder/f'R{r}M{m}.lean').write_text(text)
    patterns_text = 'def patterns : Fin 35 → Fin 4 → Fin 4 := ' + \
        vector([vector(list(map(str, slots))) for slots in patterns]) + '\n'
    for r in range(3):
        sorted_text = ''.join(f'import Math.Algebra.HiggsFourWaveCubature.R{r}M{m}\n'
                              for m in range(35))
        sorted_text += '\n/-! Bounded sorted-wave moment assembly. -/\n'
        sorted_text += 'namespace Math.HiggsFourWaveCubature\nset_option autoImplicit false\n'
        if r == 0:
            sorted_text += patterns_text
        else:
            sorted_text = 'import Math.Algebra.HiggsFourWaveCubature.Sorted0\n' + sorted_text
        sorted_text += f'theorem sorted{r} (m : Fin 35) (i j k l : Fin 4) :\n'
        sorted_text += f'    sumMoment {r} (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l =\n'
        sorted_text += f'      expected {r} (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l := by\n'
        sorted_text += '  fin_cases m <;> fin_cases i\n'
        for m in range(35):
            for i in range(4):
                sorted_text += f'  · exact moments{r}_{m}_{i} j k l\n'
        sorted_text += 'end Math.HiggsFourWaveCubature\n'
        (folder/f'Sorted{r}.lean').write_text(sorted_text)
    sorted_all = ''.join(f'import Math.Algebra.HiggsFourWaveCubature.Sorted{r}\n' for r in range(3))
    sorted_all += '\n/-! All sorted-wave fourth moments. -/\nnamespace Math.HiggsFourWaveCubature\n'
    sorted_all += 'set_option autoImplicit false\n'
    sorted_all += '''
 theorem sorted_moments (r : Fin 3) (m : Fin 35) (i j k l : Fin 4) :
    sumMoment r (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l =
      expected r (patterns m 0) (patterns m 1) (patterns m 2) (patterns m 3) i j k l := by
  fin_cases r
  · exact sorted0 m i j k l
  · exact sorted1 m i j k l
  · exact sorted2 m i j k l
end Math.HiggsFourWaveCubature
'''
    (folder/'Sorted.lean').write_text(sorted_all.replace('\n theorem','\ntheorem'))
    from itertools import product
    for s in range(4):
        text = 'import Math.Algebra.HiggsFourWaveCubature.Sorted\nimport Math.Algebra.HiggsFourWaveCubature.Symmetry\n\n'
        text += '/-! Bounded wave-slot sorting; no wave-label symmetry is presumed. -/\n'
        text += 'namespace Math.HiggsFourWaveCubature\nset_option autoImplicit false\n'
        text += f'theorem slots{s} (r : Fin 3) (t u v i j k l : Fin 4) :\n'
        text += f'    sumMoment r {s} t u v i j k l = expected r {s} t u v i j k l := by\n'
        text += '  fin_cases t <;> fin_cases u <;> fin_cases v\n'
        for tail in product(range(4), repeat=3):
            slots, directions, swaps = [s]+list(tail), list('ijkl'), []
            while slots != sorted(slots):
                a = next(i for i in range(3) if slots[i] > slots[i+1])
                slots[a], slots[a+1] = slots[a+1], slots[a]
                directions[a], directions[a+1] = directions[a+1], directions[a]
                swaps += [f'sum_swap{a}{a+1}', f'expected_swap{a}{a+1}']
            text += '  · '
            if swaps:
                text += 'rw [' + ','.join(swaps) + ']\n    '
            text += f'exact sorted_moments r {patterns.index(tuple(slots))} ' + ' '.join(directions) + '\n'
        text += 'end Math.HiggsFourWaveCubature\n'
        (folder/f'Slots{s}.lean').write_text(text)
    aggregate = ''.join(f'import Math.Algebra.HiggsFourWaveCubature.Slots{s}\n' for s in range(4))
    aggregate += '''
/-! Complete ordered fourth moments, without a group-generation premise. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
theorem moments (r : Fin 3) (s t u v i j k l : Fin 4) :
    sumMoment r s t u v i j k l = expected r s t u v i j k l := by
  fin_cases s
  · exact slots0 r t u v i j k l
  · exact slots1 r t u v i j k l
  · exact slots2 r t u v i j k l
  · exact slots3 r t u v i j k l
end Math.HiggsFourWaveCubature
'''
    Path('Math/Algebra/Waves/HiggsFourWaveCubature.lean').write_text(aggregate)
    print('Generated 288/72/72 ordered nodes and 420 structural moment derivations; finite checks only for node identities.')


if __name__ == '__main__':
    generate()
