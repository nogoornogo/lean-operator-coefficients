#!/usr/bin/env python3
"""Reproduce remaining-family node certificates; Lean checks every identity.

Reads the unchanged Basic.raw0/raw1/raw2 data. Python finds exact Gaussian-integer
reindexings, never supplies a proof premise or asserts finite-group generation.
No third-party dependencies. Run from the repository root.
"""
from pathlib import Path
from itertools import combinations, product
import re
ROOT = Path(__file__).resolve().parents[2]
folder = ROOT/'Math/Algebra/HiggsFourWaveCubature/Structural'
source = (ROOT/'Math/Algebra/HiggsFourWaveCubature/Basic.lean').read_text()
part = source.split('def raw0 ')[1].split('def raw1 ')[0]
nodes = []
for line in part.splitlines():
    values = re.findall(r'⟨(-?\d+),(-?\d+)⟩', line)
    if values:
        assert len(values) == 16
        nodes.append(tuple(tuple((int(x), int(y)) for x, y in values[i:i+4])
                           for i in range(0, 16, 4)))
assert len(nodes) == 288


def add(a, b):
    return (a[0]+b[0], a[1]+b[1])


def mul(a, b):
    return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])


phases = [(1, 0), (0, 1), (-1, 0), (0, -1)]
euclid = [tuple(tuple(mul(z, (1, 0) if i == 0 else (0, 1))
                      for i, z in enumerate(row)) for row in node) for node in nodes]
node_lookup = {node: a for a, node in enumerate(euclid)}
assert len(node_lookup) == 288
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
    assert all(indices[indices[a]] == a for a in range(288)), name
    records.append(dict(name=name, index=indices, phase=codes))

gram = [[0,8,-4,-4],[8,0,-4,-4],[-4,-4,0,8],[-4,-4,8,0]]
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


text = '''import Math.Algebra.HiggsFourWaveCubature.Structural.CollinearData

/-! Exact node transports for the unchanged 288-point transverse family. -/
namespace Math.HiggsFourWaveCubature.Structural.Transverse
set_option autoImplicit false

def euclid (a : Fin 288) (s i : Fin 4) : GaussianInt := wick i*raw 0 a s i

'''
for record in records:
    for field, typ in [('index','Fin 288'),('phase','Fin 4')]:
        text += f'\ndef {record["name"]}{field.title()} (a : Fin 288) : {typ} :=\n  '+lean_lookup(record[field],0,288)+'\n'
for field,typ in [('Index','Fin 288'),('Phase','Fin 4')]:
    text += f'\ndef swap{field} (m : Fin 6) : Fin 288 → {typ} :=\n  !['+','.join(r['name']+field for r in records[:6])+'] m\n'
text += '\ndef gramPositive (a : Fin 288) : Bool :=\n  '+lean_lookup(['true' if x==1 else 'false' for x in gram_signs],0,288)+'\n'
text += '\ndef gramSign (a : Fin 288) : GaussianInt := if gramPositive a then 1 else -1\nend Math.HiggsFourWaveCubature.Structural.Transverse\n'
(folder/'TransverseData.lean').write_text(text)
checks = '''import Math.Algebra.HiggsFourWaveCubature.Structural.TransverseData

namespace Math.HiggsFourWaveCubature.Structural.Transverse
set_option autoImplicit false
set_option Elab.async false

theorem phase_four (p : Fin 4) : phase p ^ 4 = 1 := by
  fin_cases p <;> decide +kernel

theorem gramSign_square (a : Fin 288) : gramSign a ^ 2 = 1 := by
  unfold gramSign
  split <;> ring

theorem swap_index_involutive (m : Fin 6) :
    ∀ a : Fin 288, swapIndex m (swapIndex m a) = a := by
  fin_cases m <;> decide +kernel

'''
for m in range(6):
 for t in range(4):
  checks +=f'''theorem swap_nodes_{m}_{t} : ∀ a : Fin 288, ∀ i : Fin 4,
    euclid (swapIndex {m} a) {t} i =
      phase (swapPhase {m} a)*euclid a {t} (Equiv.swap (swapLeft {m}) (swapRight {m}) i) := by
  decide +kernel

'''
checks +='''theorem swap_nodes (m : Fin 6) : ∀ a : Fin 288, ∀ s i : Fin 4,
    euclid (swapIndex m a) s i =
      phase (swapPhase m a)*euclid a s (Equiv.swap (swapLeft m) (swapRight m) i) := by
  intro a s i
  fin_cases m <;> fin_cases s
'''
for m in range(6):
 for t in range(4):checks +=f'  · exact swap_nodes_{m}_{t} a i\n'
checks +='''
theorem had_index_involutive :
    ∀ a : Fin 288, hadamardIndex (hadamardIndex a) = a := by decide +kernel

'''
for t in range(4):
 checks +=f'''theorem had_nodes_{t} : ∀ a : Fin 288,
    2*euclid (hadamardIndex a) {t} 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a {t} i) := by decide +kernel

'''
checks +='''theorem had_nodes : ∀ a : Fin 288, ∀ s : Fin 4,
    2*euclid (hadamardIndex a) s 0 =
      phase (hadamardPhase a)*(∑ i : Fin 4, euclid a s i) := by
  intro a s
  fin_cases s
'''
for t in range(4):checks +=f'  · exact had_nodes_{t} a\n'
checks +='\n'
for t in range(4):
 for u in range(4):
  checks +=f'''theorem gram_covariant_{t}_{u} : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a {t} i*euclid a {u} i) = gramSign a*gram 0 {t} {u} := by
  decide +kernel

'''
checks +='''theorem gram_covariant (s t : Fin 4) : ∀ a : Fin 288,
    (∑ i : Fin 4, euclid a s i*euclid a t i) = gramSign a*gram 0 s t := by
  intro a
  fin_cases s <;> fin_cases t
'''
for t in range(4):
 for u in range(4):checks +=f'  · exact gram_covariant_{t}_{u} a\n'
checks +='end Math.HiggsFourWaveCubature.Structural.Transverse\n'
(folder/'TransverseChecks.lean').write_text(checks)

def parse_family(r):
    stop = f'def raw{r+1} ' if r < 2 else 'def raw '
    part = source.split(f'def raw{r} ')[1].split(stop)[0]
    result = []
    for line in part.splitlines():
        values = re.findall(r'⟨(-?\d+),(-?\d+)⟩',line)
        if values:
            assert len(values) == 16
            result.append(tuple(tuple((int(x),int(y)) for x,y in values[i:i+4]) for i in range(0,16,4)))
    assert len(result) == 72
    return result

first = {node:a for a,node in enumerate(parse_family(1))}
permutation = [0,1,3,2]
indices = []
for node in parse_family(2):
    target = tuple(node[permutation[s]] for s in range(4))
    assert target in first
    indices.append(first[target])
assert all(indices[indices[a]] == a for a in range(72))
second = '''import Math.Algebra.HiggsFourWaveCubature.Structural.CollinearMoments

/-! Second-collinear nodes are the first-collinear nodes with wave labels 2 and 3 exchanged. -/
namespace Math.HiggsFourWaveCubature.Structural.SecondCollinear
set_option autoImplicit false
set_option Elab.async false
open scoped BigOperators

def wave : Fin 4 → Fin 4 := ![0,1,3,2]
def index (a : Fin 72) : Fin 72 :=
'''+'  '+lean_lookup(indices,0,72)+'\n'+'''
theorem index_involutive : ∀ a : Fin 72, index (index a) = a := by decide +kernel

theorem wave_involutive : ∀ s : Fin 4, wave (wave s) = s := by decide +kernel

theorem raw_transport : ∀ a : Fin 72, ∀ s i : Fin 4,
    raw 1 (index a) s i = raw 2 a (wave s) i := by decide +kernel

theorem gram_transport : ∀ s t : Fin 4,
    gram 1 (wave s) (wave t) = gram 2 s t := by decide +kernel

private def nodeEquiv : Fin 72 ≃ Fin 72 where
  toFun := index
  invFun := index
  left_inv := index_involutive
  right_inv := index_involutive

theorem moment_transport (s t u v i j k l : Fin 4) :
    sumMoment 1 (wave s) (wave t) (wave u) (wave v) i j k l =
      sumMoment 2 s t u v i j k l := by
  have h := Equiv.sum_comp nodeEquiv
    (fun a => raw 1 a (wave s) i*raw 1 a (wave t) j*
      raw 1 a (wave u) k*raw 1 a (wave v) l)
  change (∑ a : Fin 72, raw 1 (index a) (wave s) i*raw 1 (index a) (wave t) j*
    raw 1 (index a) (wave u) k*raw 1 (index a) (wave v) l) =
      sumMoment 1 (wave s) (wave t) (wave u) (wave v) i j k l at h
  rw [←h]
  change _ = ∑ a : Fin 72, raw 2 a s i*raw 2 a t j*raw 2 a u k*raw 2 a v l
  apply Finset.sum_congr rfl
  intro a _
  rw [raw_transport,raw_transport,raw_transport,raw_transport]
  rw [wave_involutive,wave_involutive,wave_involutive,wave_involutive]

theorem second_collinear_moments (s t u v i j k l : Fin 4) :
    sumMoment 2 s t u v i j k l = expected 2 s t u v i j k l := by
  rw [←moment_transport, collinear_moments]
  unfold expected
  simp only [gram_transport]
  rfl
end Math.HiggsFourWaveCubature.Structural.SecondCollinear
'''
(folder/'SecondCollinear.lean').write_text(second)
