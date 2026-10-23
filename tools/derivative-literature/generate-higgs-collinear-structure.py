#!/usr/bin/env python3
"""Reproduce first-collinear node transports; Lean checks every generated identity.

Reads the unchanged Basic.raw1 data. Python finds exact Gaussian-integer
reindexings, never supplies a proof premise or asserts finite-group generation.
No third-party dependencies. Run from the repository root.
"""
from pathlib import Path
from itertools import combinations, product
import re
ROOT = Path(__file__).resolve().parents[2]
folder = ROOT/'Math/Algebra/HiggsFourWaveCubature/Structural'
source = (ROOT/'Math/Algebra/HiggsFourWaveCubature/Basic.lean').read_text()
part = source.split('def raw1 ')[1].split('def raw2 ')[0]
nodes = []
for line in part.splitlines():
    values = re.findall(r'⟨(-?\d+),(-?\d+)⟩', line)
    if values:
        assert len(values) == 16
        nodes.append(tuple(tuple((int(x), int(y)) for x, y in values[i:i+4])
                           for i in range(0, 16, 4)))
assert len(nodes) == 72


def add(a, b):
    return (a[0]+b[0], a[1]+b[1])


def mul(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


phases = [(1, 0), (0, 1), (-1, 0), (0, -1)]
euclid = [tuple(tuple(mul(z, (1, 0) if i == 0 else (0, 1))
                      for i, z in enumerate(row)) for row in node) for node in nodes]
node_lookup = {node: a for a, node in enumerate(euclid)}
assert len(node_lookup) == 72
operations = [('swap'+str(i)+str(j), (i, j)) for i, j in combinations(range(4), 2)]
operations.append(('hadamard', None))
records = []
for name, pair in operations:
    indices, codes = [], []
    for node in euclid:
        if pair:
            i, j = pair
            permutation = list(range(4))
            permutation[i], permutation[j] = permutation[j], permutation[i]
            transformed = tuple(tuple(row[permutation[k]] for k in range(4)) for row in node)
        else:
            transformed = []
            for row in node:
                result = []
                for i in range(4):
                    z = (0, 0)
                    for j in range(4):
                        z = add(z, mul(((-1)**((i & j).bit_count()), 0), row[j]))
                    assert z[0] % 2 == z[1] % 2 == 0
                    result.append((z[0]//2, z[1]//2))
                transformed.append(tuple(result))
            transformed = tuple(transformed)
        choices = []
        for code, phase in enumerate(phases):
            image = tuple(tuple(mul(phase, z) for z in row) for row in transformed)
            if image in node_lookup:
                choices.append((node_lookup[image], code))
        assert len(choices) == 1, (name, len(choices))
        index, code = choices[0]
        indices.append(index)
        codes.append(code)
    assert all(indices[indices[a]] == a for a in range(72)), name
    records.append(dict(name=name, index=indices, phase=codes))

gram = [[0, 8, 0, -8], [8, 0, -8, 0], [0, -8, 0, 8], [-8, 0, 8, 0]]
gram_signs = []
for node in euclid:
    base = (0, 0)
    for i in range(4):
        base = add(base, mul(node[0][i], node[1][i]))
    assert base in [(8, 0), (-8, 0)]
    sign = base[0]//8
    gram_signs.append(sign)
    for s, t in product(range(4), repeat=2):
        total = (0, 0)
        for i in range(4):
            total = add(total, mul(node[s][i], node[t][i]))
        assert total == (sign*gram[s][t], 0)


def lean_lookup(values, start, stop, indent='  '):
    if len(set(values[start:stop])) == 1:
        return str(values[start])
    middle = (start+stop)//2
    return (f'if a.val < {middle} then\n{indent}  ' +
            lean_lookup(values, start, middle, indent+'  ') +
            f'\n{indent}else\n{indent}  ' +
            lean_lookup(values, middle, stop, indent+'  '))


text='''import Math.Algebra.HiggsFourWaveCubature.Structural.TensorShape

/-! Exact node transports for the unchanged 72-point first-collinear family. -/
namespace Math.HiggsFourWaveCubature.Structural
set_option autoImplicit false

def wick (i : Fin 4) : GaussianInt := if i=0 then 1 else ⟨0,1⟩
def euclid (a : Fin 72) (s i : Fin 4) : GaussianInt := wick i*raw 1 a s i
def phase (p : Fin 4) : GaussianInt := ![1,⟨0,1⟩,-1,⟨0,-1⟩] p

def swapLeft : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def swapRight : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
'''
for rec in records:
    name = rec['name']
    for field,typ in [('index','Fin 72'),('phase','Fin 4')]:
        text += f'\ndef {name}{field.title()} (a : Fin 72) : {typ} :=\n  '+lean_lookup(rec[field],0,72)+'\n'
for field,typ in [('Index','Fin 72'),('Phase','Fin 4')]:
    text += f'\ndef swap{field} (m : Fin 6) : Fin 72 → {typ} :=\n  !['+','.join(r['name']+field for r in records[:6])+'] m\n'
vals=['true' if x==1 else 'false' for x in gram_signs]
text+='\ndef gramPositive (a : Fin 72) : Bool :=\n  '+lean_lookup(vals,0,72)+'\n'
text+='''
def gramSign (a : Fin 72) : GaussianInt := if gramPositive a then 1 else -1
end Math.HiggsFourWaveCubature.Structural
'''
(folder/'CollinearData.lean').write_text(text)
cert='''import Math.Algebra.HiggsFourWaveCubature.Structural.CollinearData

namespace Math.HiggsFourWaveCubature.Structural
set_option autoImplicit false
set_option Elab.async false

theorem phase_four (p : Fin 4) : phase p ^ 4 = 1 := by
  fin_cases p <;> decide +kernel

theorem gramSign_square (a : Fin 72) : gramSign a ^ 2 = 1 := by
  unfold gramSign
  split <;> ring

theorem swap_index_involutive (m : Fin 6) :
    ∀ a : Fin 72, swapIndex m (swapIndex m a) = a := by
  fin_cases m <;> decide +kernel

theorem swap_nodes (m : Fin 6) : ∀ a : Fin 72, ∀ s i : Fin 4,
    euclid (swapIndex m a) s i =
      phase (swapPhase m a)*euclid a s (Equiv.swap (swapLeft m) (swapRight m) i) := by
  fin_cases m <;> decide +kernel

theorem had_index_involutive :
    ∀ a : Fin 72, hadamardIndex (hadamardIndex a) = a := by decide +kernel

theorem had_nodes : ∀ a : Fin 72, ∀ s : Fin 4,
    2*euclid (hadamardIndex a) s 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a s i) := by decide +kernel

theorem gram_covariant (s t : Fin 4) : ∀ a : Fin 72,
    (∑ i : Fin 4, euclid a s i*euclid a t i) = gramSign a*gram 1 s t := by
  fin_cases s <;> fin_cases t <;> decide +kernel
end Math.HiggsFourWaveCubature.Structural
'''
(folder/'CollinearChecks.lean').write_text(cert)
