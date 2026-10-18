import Math.RepresentationTheory.ExternalInvariantTensor
import TauCeti.RepresentationTheory.ExteriorPower
import Mathlib.Tactic

/-!
# Alternating six-slot coefficients with species pattern (A,B,A,B,B,B)

The ordered input is grouped as three pairs. The exterior carrier is the
direct sum of the two species. This file supplies only alternating descent;
it makes no claim that all degree-(2,4) coefficients arise this way.
-/

namespace Math.SixSlotAlternation

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section

open Representation
open scoped TensorProduct

variable {H A B : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

abbrev Fields (A B : Type*) := A × B

abbrev OrderedSpace (A B : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] :=
  (((A ⊗[ℂ] B) ⊗[ℂ] (A ⊗[ℂ] B)) ⊗[ℂ] (B ⊗[ℂ] B))

def ordered (f : OrderedSpace A B →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin 6 => Fields A B) ℂ :=
  MultilinearMap.mk'
    (fun v => f ((((v 0).1 ⊗ₜ[ℂ] (v 1).2) ⊗ₜ[ℂ]
      ((v 2).1 ⊗ₜ[ℂ] (v 3).2)) ⊗ₜ[ℂ] ((v 4).2 ⊗ₜ[ℂ] (v 5).2)))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update, TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by intro v i c x; fin_cases i <;>
      simp [Function.update, TensorProduct.smul_tmul, TensorProduct.tmul_smul])

def alternating (f : OrderedSpace A B →ₗ[ℂ] ℂ) :
    Fields A B [⋀^Fin 6]→ₗ[ℂ] ℂ := (ordered f).alternatization

theorem alternating_smul (c : ℂ) (f : OrderedSpace A B →ₗ[ℂ] ℂ)
    (v : Fin 6 → Fields A B) :
    alternating (c • f) v = c • alternating f v := by
  classical
  simp only [alternating, ordered, MultilinearMap.alternatization_apply,
    MultilinearMap.domDomCongr_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  change Equiv.Perm.sign p •
      (c * f ((((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).2) ⊗ₜ[ℂ]
        ((v (p 2)).1 ⊗ₜ[ℂ] (v (p 3)).2)) ⊗ₜ[ℂ]
          ((v (p 4)).2 ⊗ₜ[ℂ] (v (p 5)).2))) =
    c * (Equiv.Perm.sign p •
      f ((((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).2) ⊗ₜ[ℂ]
        ((v (p 2)).1 ⊗ₜ[ℂ] (v (p 3)).2)) ⊗ₜ[ℂ]
          ((v (p 4)).2 ⊗ₜ[ℂ] (v (p 5)).2)))
  simpa only [smul_eq_mul] using
    (smul_comm (Equiv.Perm.sign p) c
      (f ((((v (p 0)).1 ⊗ₜ[ℂ] (v (p 1)).2) ⊗ₜ[ℂ]
        ((v (p 2)).1 ⊗ₜ[ℂ] (v (p 3)).2)) ⊗ₜ[ℂ]
          ((v (p 4)).2 ⊗ₜ[ℂ] (v (p 5)).2))))

def slots (u₁ u₂ : A) (d₁ d₂ d₃ d₄ : B) : Fin 6 → Fields A B :=
  ![(u₁, 0), (0, d₁), (u₂, 0), (0, d₂), (0, d₃), (0, d₄)]

/-- Permutations which put the two `A` inputs back into the two slots read by
`ordered`.  Bijectivity then forces the four remaining inputs into `B` slots. -/
def PreservesPattern (p : Equiv.Perm (Fin 6)) : Prop :=
  (p 0 = 0 ∨ p 0 = 2) ∧ (p 2 = 0 ∨ p 2 = 2)

instance (p : Equiv.Perm (Fin 6)) : Decidable (PreservesPattern p) :=
  inferInstanceAs (Decidable ((_ ∨ _) ∧ (_ ∨ _)))

theorem preservesPattern_card :
    (Finset.univ.filter PreservesPattern).card = 48 := by decide +kernel

/-- On pure `(A,B,A,B,B,B)` inputs, full six-slot alternatization is the
`2! 4! = 48` multiple of an ordered contraction which already has the correct
sign under every within-species permutation. -/
theorem alternating_slots_of_preserves
    (f : OrderedSpace A B →ₗ[ℂ] ℂ) (u₁ u₂ : A) (d₁ d₂ d₃ d₄ : B)
    (hperm : ∀ p : Equiv.Perm (Fin 6), PreservesPattern p →
      ordered f (slots u₁ u₂ d₁ d₂ d₃ d₄ ∘ p) =
        Equiv.Perm.sign p •
          f ((((u₁ ⊗ₜ[ℂ] d₁) ⊗ₜ[ℂ] (u₂ ⊗ₜ[ℂ] d₂)) ⊗ₜ[ℂ]
            (d₃ ⊗ₜ[ℂ] d₄)))) :
    alternating f (slots u₁ u₂ d₁ d₂ d₃ d₄) =
      48 • f ((((u₁ ⊗ₜ[ℂ] d₁) ⊗ₜ[ℂ] (u₂ ⊗ₜ[ℂ] d₂)) ⊗ₜ[ℂ]
        (d₃ ⊗ₜ[ℂ] d₄))) := by
  classical
  unfold alternating
  rw [MultilinearMap.alternatization_apply]
  let good : Finset (Equiv.Perm (Fin 6)) := Finset.univ.filter PreservesPattern
  have hsubset : good ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_subset hsubset]
  · calc
      ∑ p ∈ good, Equiv.Perm.sign p •
          ordered f (slots u₁ u₂ d₁ d₂ d₃ d₄ ∘ p) =
          ∑ _p ∈ good,
            f ((((u₁ ⊗ₜ[ℂ] d₁) ⊗ₜ[ℂ] (u₂ ⊗ₜ[ℂ] d₂)) ⊗ₜ[ℂ]
              (d₃ ⊗ₜ[ℂ] d₄))) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [hperm p (Finset.mem_filter.mp hp).2, smul_smul]
            simp
      _ = 48 • f ((((u₁ ⊗ₜ[ℂ] d₁) ⊗ₜ[ℂ] (u₂ ⊗ₜ[ℂ] d₂)) ⊗ₜ[ℂ]
            (d₃ ⊗ₜ[ℂ] d₄))) := by
          rw [Finset.sum_const, nsmul_eq_mul, preservesPattern_card]
          norm_num
  · intro p _ hp
    have hbad : ¬ PreservesPattern p := by
      simpa [good] using hp
    by_cases h0 : p 0 = 0 ∨ p 0 = 2
    · have h2 : ¬ (p 2 = 0 ∨ p 2 = 2) := fun h => hbad ⟨h0, h⟩
      generalize hk : p 2 = k
      fin_cases k <;> simp_all [ordered, slots, PreservesPattern]
    · generalize hk : p 0 = k
      fin_cases k <;> simp_all [ordered, slots, PreservesPattern]

variable (a : Representation ℂ H A) (b : Representation ℂ H B)

abbrev action := a.prod b

abbrev orderedRepresentation :=
  (((a.tprod b).tprod (a.tprod b)).tprod (b.tprod b))

theorem alternating_invariant
    (f : IntertwiningMap (orderedRepresentation a b) (Representation.trivial ℂ H ℂ))
    (g : H) (v : Fin 6 → Fields A B) :
    alternating f.toLinearMap (fun i => action a b g (v i)) =
      alternating f.toLinearMap v := by
  simp only [alternating, MultilinearMap.alternatization_apply]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  change f (orderedRepresentation a b g
    ((((v (s 0)).1 ⊗ₜ[ℂ] (v (s 1)).2) ⊗ₜ[ℂ]
      ((v (s 2)).1 ⊗ₜ[ℂ] (v (s 3)).2)) ⊗ₜ[ℂ]
        ((v (s 4)).2 ⊗ₜ[ℂ] (v (s 5)).2))) = _
  exact IntertwiningMap.isIntertwining _ _ f g _

def coefficient
    (f : IntertwiningMap (orderedRepresentation a b) (Representation.trivial ℂ H ℂ)) :
    IntertwiningMap ((action a b).exteriorPower 6)
      (Representation.trivial ℂ H ℂ) where
  toLinearMap := exteriorPower.alternatingMapLinearEquiv (alternating f.toLinearMap)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Representation.exteriorPower_apply_ιMulti,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact alternating_invariant a b f g v

theorem coefficient_apply_ιMulti
    (f : IntertwiningMap (orderedRepresentation a b) (Representation.trivial ℂ H ℂ))
    (v : Fin 6 → Fields A B) :
    coefficient a b f (exteriorPower.ιMulti ℂ 6 v) = alternating f.toLinearMap v := by
  change exteriorPower.alternatingMapLinearEquiv _ _ = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

theorem coefficient_ne_zero_of_evaluation
    (f : IntertwiningMap (orderedRepresentation a b) (Representation.trivial ℂ H ℂ))
    (v : Fin 6 → Fields A B) (h : alternating f.toLinearMap v ≠ 0) :
    coefficient a b f ≠ 0 := by
  intro hz
  have he := coefficient_apply_ιMulti a b f v
  rw [hz] at he
  exact h he.symm

end
end Math.SixSlotAlternation
