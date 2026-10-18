import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-! Positive homogeneous exterior kernels have finite exact inverses.
The nilpotence bound is proved from a finite spanning family. -/
namespace Math.ExteriorNilpotentKernel
set_option autoImplicit false
noncomputable section
open scoped Matrix
variable {k V I J : Type*} [Field k] [AddCommGroup V] [Module k V]
  [Fintype I] [DecidableEq I] [Fintype J]

abbrev A := ExteriorAlgebra k V
abbrev P : Submodule k (A (k := k) (V := V)) :=
  LinearMap.range (ExteriorAlgebra.ι k : V →ₗ[k] ExteriorAlgebra k V)

theorem power_entries (T : Matrix I I (A (k := k) (V := V))) (d : ℕ)
    (hT : ∀ i j, T i j ∈ (P (k := k) (V := V))^d) (n : ℕ) :
    ∀ i j, (T^n) i j ∈ (P (k := k) (V := V))^(d*n) := by
  induction n with
  | zero =>
    intro i j
    simp only [pow_zero, Nat.mul_zero]
    by_cases h : i = j
    · subst j
      simp
    · simp [h]
  | succ n ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    apply Submodule.sum_mem
    intro l _
    have h := Submodule.mul_mem_mul (ih i l) (hT l j)
    simpa [← pow_add, Nat.mul_succ] using h

theorem nilpotent (g : J → V) (hg : Submodule.span k (Set.range g) = ⊤)
    (T : Matrix I I (A (k := k) (V := V))) (d n : ℕ)
    (hT : ∀ i j, T i j ∈ (P (k := k) (V := V))^d)
    (hn : Fintype.card J < d*n) : T^n = 0 := by
  have : Subsingleton (⋀[k]^(d*n) V) :=
    exteriorPower.subsingleton_of_span_eq_top_of_card_lt g hg (d*n)
      (by simpa [Nat.card_eq_fintype_card] using hn)
  ext i j
  have h := power_entries T d hT n i j
  exact congrArg Subtype.val (Subsingleton.elim (⟨(T^n) i j, h⟩ : ⋀[k]^(d*n) V) 0)

def inverse (T : Matrix I I (A (k := k) (V := V))) (N : ℕ) :=
  ∑ i ∈ Finset.range N, T^i

theorem inverse_left (T : Matrix I I (A (k := k) (V := V))) (N : ℕ)
    (hT : T^N = 0) : inverse T N * (1-T) = 1 := by
  simpa [inverse, hT] using geom_sum_mul_neg T N

theorem inverse_right (T : Matrix I I (A (k := k) (V := V))) (N : ℕ)
    (hT : T^N = 0) : (1-T) * inverse T N = 1 := by
  simpa [inverse, hT] using mul_neg_geom_sum T N

def solution (T : Matrix I I (A (k := k) (V := V))) (N : ℕ)
    (s : I → A (k := k) (V := V)) := (inverse T N) *ᵥ s

theorem source_equation (T : Matrix I I (A (k := k) (V := V))) (N : ℕ)
    (hT : T^N = 0) (s : I → A (k := k) (V := V)) :
    solution T N s - T *ᵥ solution T N s = s := by
  have h := congrArg (fun K => K *ᵥ s) (inverse_right T N hT)
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact h

theorem unique (T : Matrix I I (A (k := k) (V := V))) (N : ℕ)
    (hT : T^N = 0) (s x : I → A (k := k) (V := V))
    (hx : x-T *ᵥ x = s) : x = solution T N s := by
  have h := congrArg (fun K => K *ᵥ x) (inverse_left T N hT)
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hx] at h
  exact h.symm

end
end Math.ExteriorNilpotentKernel
