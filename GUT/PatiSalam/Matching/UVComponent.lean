import Mathlib.Tactic

/-! Finite oriented epsilon component of the supplied PS contraction.
A tensor-invariance and full UV branching certificate is not claimed. -/
namespace GUT.PatiSalam.UVComponent
set_option autoImplicit false

def epsilon (xs : List ℕ) : ℤ :=
  if xs.Nodup then
    (-1) ^ ((List.range xs.length).map (fun i => (xs.drop (i+1)).countP (fun y => xs[i]! > y))).sum
  else 0

/-- Both orders of the symmetric fermion bilinear and commuting scalar pair. -/
def component (a b c : Fin 3) : ℤ :=
  epsilon [a,b,c,3] * epsilon [1,0] * epsilon [1,0] +
  epsilon [b,a,c,3] * epsilon [0,1] * epsilon [1,0] +
  epsilon [a,b,3,c] * epsilon [1,0] * epsilon [0,1] +
  epsilon [b,a,3,c] * epsilon [0,1] * epsilon [0,1]

theorem component_eq_four (a b c : Fin 3) : component a b c = 4 * epsilon [a,b,c] := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

theorem component_nonzero : component 0 1 2 = 4 := by decide +kernel

/-- Before resolving the two Q weak components, only the scalar pair is expanded. -/
def leftCovariant (a b c : Fin 3) (i j : Fin 2) : ℤ :=
  epsilon [a,b,c,3] * epsilon [i,j] * epsilon [1,0] +
  epsilon [a,b,3,c] * epsilon [i,j] * epsilon [0,1]

theorem leftCovariant_eq (a b c : Fin 3) (i j : Fin 2) :
    leftCovariant a b c i j = -2 * epsilon [a,b,c] * epsilon [i,j] := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> fin_cases j <;> decide +kernel

/-- Resolving the two Q components reproduces the diquark component factor four. -/
theorem left_component_relation (a b c : Fin 3) :
    leftCovariant a b c 1 0 + leftCovariant b a c 0 1 = component a b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide +kernel

end GUT.PatiSalam.UVComponent
