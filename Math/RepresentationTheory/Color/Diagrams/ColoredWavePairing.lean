import Math.Algebra.Waves.ColoredFourWavePolarization
import Math.RepresentationTheory.Constructions.PairedComponentFields
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Exact internal coevaluation for ordered colored waves. -/
namespace Math.ColoredWavePairing
set_option autoImplicit false
noncomputable section
open ColoredFourWavePolarization PairedComponentFields
abbrev Label := Bool × Fin 2
abbrev Fields := JetLinear.Field Label

def pair (v w : Fields) : ℂ := (fieldEquiv v).2 (fieldEquiv w).1
theorem pair_add_left (u v w : Fields) : pair (u+v) w = pair u w+pair v w := by simp [pair]
theorem pair_add_right (u v w : Fields) : pair u (v+w) = pair u v+pair u w := by simp [pair]
theorem pair_smul_left (c : ℂ) (u v : Fields) : pair (c • u) v = c*pair u v := by simp [pair]
theorem pair_smul_right (c : ℂ) (u v : Fields) : pair u (c • v) = c*pair u v := by simp [pair]

theorem pair_invariant {H : Type*} [Group H] (rho : Representation ℂ H (Fin 2 → ℂ))
    (g : H) (v w : Fields) : pair (action rho g v) (action rho g w) = pair v w := by
  simp only [pair,fieldEquiv_action]
  change (fieldEquiv v).2 (rho g⁻¹ (rho g (fieldEquiv w).1)) = _
  rw [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,Module.End.one_apply]

def pairInt (j k : Label) : ℤ := if j.1 = true ∧ k.1 = false ∧ j.2 = k.2 then 1 else 0
theorem pair_single (j k : Label) :
    pair (Finsupp.single j 1) (Finsupp.single k 1) = (pairInt j k : ℂ) := by
  rcases j with ⟨c,a⟩
  rcases k with ⟨d,b⟩
  cases c <;> cases d <;> fin_cases a <;> fin_cases b
  all_goals simp [pair,pairInt,fieldEquiv_false,fieldEquiv_true,dual_basis]

def base : MultilinearMap ℂ (fun _ : Fin 4 => Fields) ℂ :=
  MultilinearMap.mk' (fun v => pair (v 2) (v 0)*pair (v 3) (v 1))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update,Fin.ext_iff,pair_add_left,pair_add_right,mul_add,add_mul])
    (by intro v i c x; fin_cases i <;>
      simp [Function.update,Fin.ext_iff,pair_smul_left,pair_smul_right] <;> ring)

def tensor (p : Fin 24) : MultilinearMap ℂ (fun _ : Fin 4 => Fields) ℂ :=
  base.domDomCongr (permutation p).symm
theorem tensor_apply (p : Fin 24) (v : Fin 4 → Fields) :
    tensor p v = pair (v (inverses p 2)) (v (inverses p 0))*
      pair (v (inverses p 3)) (v (inverses p 1)) := rfl

theorem tensor_invariant {H : Type*} [Group H] (rho : Representation ℂ H (Fin 2 → ℂ))
    (p : Fin 24) (g : H) (v : Fin 4 → Fields) :
    tensor p (fun t => action rho g (v t)) = tensor p v := by
  simp only [tensor_apply,pair_invariant]

def amplitudeInt (x y : Fin 2) (j : Label) (s : Fin 4) : ℤ :=
  if j.1 then
    if s = 2 then if j.2 = x then 1 else 0
    else if s = 3 then if j.2 = y then 1 else 0 else 0
  else
    if s = 0 then if j.2 = x then 1 else 0
    else if s = 1 then if j.2 = y then 1 else 0 else 0
def amplitudes (x y : Fin 2) (j : Label) (s : Fin 4) : ℂ := amplitudeInt x y j s
def internalInt (a : Fin 4 → Label) (p : Fin 24) : ℤ :=
  ∑ x : Fin 2, ∑ y : Fin 2, amplitudeProduct (amplitudeInt x y) a p

theorem integer_pairing : ∀ p : Fin 24, ∀ a b c d : Label,
    internalInt ![a,b,c,d] p =
      pairInt (![a,b,c,d] (inverses p 2)) (![a,b,c,d] (inverses p 0))*
      pairInt (![a,b,c,d] (inverses p 3)) (![a,b,c,d] (inverses p 1)) := by decide +kernel

theorem internalInt_pairing (a : Fin 4 → Label) (p : Fin 24) :
    internalInt a p = pairInt (a (inverses p 2)) (a (inverses p 0))*
      pairInt (a (inverses p 3)) (a (inverses p 1)) := by
  have ha : ![a 0,a 1,a 2,a 3] = a := by funext t; fin_cases t <;> rfl
  simpa only [ha] using integer_pairing p (a 0) (a 1) (a 2) (a 3)

theorem amplitude_sum_pairing (a : Fin 4 → Label) (p : Fin 24) :
    (∑ x : Fin 2, ∑ y : Fin 2, amplitudeProduct (amplitudes x y) a p) =
      tensor p (fun t => Finsupp.single (a t) 1) := by
  rw [tensor_apply,pair_single,pair_single,← Int.cast_mul,← internalInt_pairing]
  simp only [internalInt,amplitudeProduct,amplitudes,Int.cast_sum,Int.cast_mul]

theorem tensor_basis_int (a : Fin 4 → Label) (p : Fin 24) :
    tensor p (fun t => Finsupp.single (a t) 1) = (internalInt a p : ℂ) := by
  rw [tensor_apply,pair_single,pair_single,← Int.cast_mul,← internalInt_pairing]

end
end Math.ColoredWavePairing
