import Math.RepresentationTheory.FiniteLocalBasisConversion
import Mathlib.Tactic

/-! A concrete non-diagonal two-contraction dictionary conversion. Flavor and
its residual symmetry remain arbitrary; both dictionaries are proved complete. -/
namespace Math.FiniteLocalBasisConversionControls
set_option autoImplicit false
noncomputable section
open Representation

abbrev A := Fin 2 → ℂ
abbrev localRep := Representation.trivial ℂ Unit A

def p (i : Fin 2) : IntertwiningMap localRep (Representation.trivial ℂ Unit ℂ) where
  toLinearMap := LinearMap.proj i
  isIntertwining' _ := rfl

def v (i : Fin 2) : A := Pi.single i 1

@[simp] theorem p_apply (i : Fin 2) (u : A) : p i u = u i := rfl

theorem normalized : ∀ i j, p i (v j) = if i = j then 1 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [v]

theorem complete (f : IntertwiningMap localRep (Representation.trivial ℂ Unit ℂ)) :
    f = ∑ i, f (v i) • p i := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  have hu : u = u 0 • v 0 + u 1 • v 1 := by
    ext i
    fin_cases i <;> simp [v]
  have hf := congrArg f hu
  simpa [Fin.sum_univ_two, smul_eq_mul, mul_comm] using hf

def q (i : Fin 2) : IntertwiningMap localRep (Representation.trivial ℂ Unit ℂ) :=
  if i = 0 then p 0 + p 1 else p 0 - p 1

def w (i : Fin 2) : A :=
  if i = 0 then (1 / 2 : ℂ) • (v 0 + v 1) else (1 / 2 : ℂ) • (v 0 - v 1)

theorem mixed_normalized : ∀ i j, q i (w j) = if i = j then 1 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [q, w, v]

theorem mixed_complete (f : IntertwiningMap localRep (Representation.trivial ℂ Unit ℂ)) :
    f = ∑ i, f (w i) • q i := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  have h := congrArg (fun t : IntertwiningMap localRep
      (Representation.trivial ℂ Unit ℂ) => t u) (complete f)
  simp [Fin.sum_univ_two, q, w,
    smul_eq_mul] at h ⊢
  linear_combination h

variable {H X : Type*} [Group H] [AddCommMonoid X] [Module ℂ X]
  (x : Representation ℂ H X)

def conversion := FiniteLocalBasisConversion.equiv localRep x p v normalized complete
  q w mixed_normalized mixed_complete

theorem forward_zero (c : Fin 2 → IntertwiningMap x (Representation.trivial ℂ H ℂ))
    (u : X) : conversion x c 0 u = (c 0 u + c 1 u) / 2 := by
  unfold conversion
  rw [FiniteLocalBasisConversion.equiv_apply]
  simp [Fin.sum_univ_two, w, v]
  ring

theorem forward_one (c : Fin 2 → IntertwiningMap x (Representation.trivial ℂ H ℂ))
    (u : X) : conversion x c 1 u = (c 0 u - c 1 u) / 2 := by
  unfold conversion
  rw [FiniteLocalBasisConversion.equiv_apply]
  simp [Fin.sum_univ_two, w, v]
  ring

theorem inverse_zero (c : Fin 2 → IntertwiningMap x (Representation.trivial ℂ H ℂ))
    (u : X) : (conversion x).symm c 0 u = c 0 u + c 1 u := by
  unfold conversion
  rw [FiniteLocalBasisConversion.inverse_apply]
  simp [Fin.sum_univ_two, q, v]

theorem inverse_one (c : Fin 2 → IntertwiningMap x (Representation.trivial ℂ H ℂ))
    (u : X) : (conversion x).symm c 1 u = c 0 u - c 1 u := by
  unfold conversion
  rw [FiniteLocalBasisConversion.inverse_apply]
  simp [Fin.sum_univ_two, q, v, sub_eq_add_neg]

end
end Math.FiniteLocalBasisConversionControls
