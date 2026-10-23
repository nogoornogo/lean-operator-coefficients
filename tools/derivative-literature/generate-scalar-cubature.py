#!/usr/bin/env python3
"""Generate a 36-wave exact cubature candidate and Lean certificates.

The finite F4 construction is a reproducible way to find the data. Its group
order and orbit count are not proof premises: Lean checks conservation,
nullness and all moment identities directly on the displayed integer data.
Only the standard library is used. Run from the repository root.
"""
from collections import deque, Counter
from pathlib import Path
I=tuple(tuple(2*int(i==j) for j in range(4)) for i in range(4))
gens=[]
for p in [(1,0,2,3),(0,2,1,3),(0,1,3,2)]:gens.append(tuple(tuple(2*int(p[i]==j) for j in range(4)) for i in range(4)))
gens.append(tuple(tuple((-2 if i==0 else 2)*int(i==j) for j in range(4)) for i in range(4)))
gens.append(tuple(tuple((-1)**(bin(i&j).count('1')) for j in range(4)) for i in range(4)))
def mul(A,B):
 r=tuple(tuple(sum(A[i][k]*B[k][j] for k in range(4)) for j in range(4)) for i in range(4))
 assert all(x%2==0 for row in r for x in row)
 return tuple(tuple(x//2 for x in row) for row in r)
q=deque([I]);seen={I}
while q:
 A=q.popleft()
 for B in gens:
  C=mul(A,B)
  if C not in seen:seen.add(C);q.append(C)
assert len(seen)==1152
assert all(sum(A[i][k]*A[j][k] for k in range(4))==4*int(i==j) for A in seen for i in range(4) for j in range(4))
# Gaussian integers are pairs, avoiding floating point or third-party code.
def phase(z,p):
 a,b=z
 return [(a,b),(-b,a),(-a,-b),(b,-a)][p]
def canonical(k):return min(tuple(sorted(tuple(phase(z,p) for z in row) for row in k)) for p in range(4))
base=[[(1,0),(0,0),(0,0),(0,1)],[(1,0),(0,0),(0,0),(0,-1)],[(-1,0),(0,-1),(0,0),(0,0)],[(-1,0),(0,1),(0,0),(0,0)]]
counts=Counter()
for A in sorted(seen):
 k=[]
 for s in base:
  e=[tuple(sum(A[i][j]*s[j][part] for j in range(4)) for part in range(2)) for i in range(4)]
  k.append([e[0]]+[phase(z,3) for z in e[1:]])
 counts[canonical(k)]+=1
assert len(counts)==36 and set(counts.values())=={32}
configs=sorted(counts)
directory=Path('Math/Algebra/ScalarFourWaveCubature')
directory.mkdir(exist_ok=True)
raw='![\n  '+',\n  '.join('!['+', '.join('!['+', '.join(f'⟨{a},{b}⟩' for a,b in row)+']' for row in k)+']' for k in configs)+'\n]'
basic='''import Math.Algebra.Waves.FourWavePolarization
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Exact finite null-wave data. Generated data have no oracle status;
the algebraic identities are checked in the dependent proof modules. -/
namespace Math.ScalarFourWaveCubature
set_option autoImplicit false
open FourWavePolarization

def raw : Fin 36 → Fin 4 → Fin 4 → GaussianInt :=
  '''+raw+'''

def metric (i j : Fin 4) : GaussianInt := if i = j then (if i = 0 then 1 else -1) else 0
def alpha : Fin 5 → ℤ := ![0,0,-768,384,1152]
def beta : Fin 5 → ℤ := ![0,0,1536,-768,1152]
def expected (r : Fin 5) (i j k l : Fin 4) : GaussianInt :=
  (alpha r : GaussianInt)*(metric i j*metric k l)+
  (beta r : GaussianInt)*(metric i k*metric j l+metric i l*metric j k)
def sumMoment (r : Fin 5) (i j k l : Fin 4) : GaussianInt :=
  ∑ a : Fin 36, moment (raw a) r i j k l

theorem conservation : ∀ a : Fin 36, ∀ i : Fin 4, (∑ s : Fin 4, raw a s i) = 0 := by
  decide +kernel
theorem null : ∀ a : Fin 36, ∀ s : Fin 4,
    (raw a s 0)^2-(raw a s 1)^2-(raw a s 2)^2-(raw a s 3)^2 = 0 := by
  decide +kernel

end Math.ScalarFourWaveCubature
'''
(directory/'Basic.lean').write_text(basic)
previous='Basic'
for r in range(5):
 text=f'import Math.Algebra.ScalarFourWaveCubature.{previous}\n\n'
 text+='/-! Generated exact moment identities, checked by kernel reduction. -/\n'
 text+='namespace Math.ScalarFourWaveCubature\nset_option autoImplicit false\n\n'
 for i in range(4):
  text+=f'theorem moments{r}{i} : ∀ j k l : Fin 4, sumMoment {r} {i} j k l = expected {r} {i} j k l := by\n  decide +kernel\n\n'
 text+='end Math.ScalarFourWaveCubature\n'
 previous=f'Moments{r}'
 (directory/(previous+'.lean')).write_text(text)
text=f'import Math.Algebra.ScalarFourWaveCubature.{previous}\n\n'
text+='/-! Complete finite moment table; no finite group theorem is assumed. -/\n'
text+='namespace Math.ScalarFourWaveCubature\nset_option autoImplicit false\n\n'
text+='theorem moments (r : Fin 5) (i j k l : Fin 4) : sumMoment r i j k l = expected r i j k l := by\n'
text+='  fin_cases r <;> fin_cases i\n'
for r in range(5):
 for i in range(4):text+=f'  · exact moments{r}{i} j k l\n'
text+='\nend Math.ScalarFourWaveCubature\n'
Path('Math/Algebra/Waves/ScalarFourWaveCubature.lean').write_text(text)
print('Generated 36 Gaussian-integer configurations; conservation, nullness and moments require Lean checking.')
