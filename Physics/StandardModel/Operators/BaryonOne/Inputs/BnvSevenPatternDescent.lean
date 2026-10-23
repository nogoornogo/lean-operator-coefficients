import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvMixedWeylSupport
import Math.RepresentationTheory.Content.MixedSinglePatternAssembly

open Math

/-! Two-sided typed descent for the dimension-seven matter/Higgs patterns.
This is an input/exchange equivalence, not yet the local residual-Hom dictionary. -/
namespace Physics.BnvSevenPatternDescent
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput

def pattern (p : Fin 4) : Fin 4 → Species := match p with
  | 0 => ![1,2,2,8]
  | 1 => ![0,0,2,8]
  | 2 => ![0,2,2,9]
  | 3 => ![2,2,2,8]

def scalar (p : Fin 4) : BnvMixedInput.ScalarSpecies := if p = 3 then 0 else 1

theorem pattern_counts (p : Fin 4) :
    counts (pattern p) =
      (![BnvBoundedSpecies.uddAntiL, BnvBoundedSpecies.qqdAntiL,
        BnvBoundedSpecies.qddAntiE, BnvBoundedSpecies.dddAntiL] p).fermions := by
  fin_cases p <;>
    decide +kernel

theorem pattern_baryon (p : Fin 4) : ∑ i, baryon (pattern p i) = 3 := by
  fin_cases p <;> norm_num [pattern, baryon, Fin.sum_univ_succ]

theorem pattern_hypercharge (p : Fin 4) :
    (∑ i, hypercharge (pattern p i)) + BnvMixedInput.scalarHypercharge (scalar p) = 0 := by
  fin_cases p <;> norm_num [pattern, scalar, hypercharge,
    BnvMixedInput.scalarHypercharge, Fin.sum_univ_succ]

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

/-- Independent full-species coefficients supported on one typed orbit. -/
abbrev family (p : Fin 4) := MixedSinglePatternAssembly.familySpace
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
  (pattern p) (scalar p)

/-- Actual gauge, Weyl, residual and identical-fermion exchange constraints. -/
abbrev ordered (p : Fin 4) := MixedSinglePatternAssembly.orderedSpace
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)
  (pattern p) (scalar p)

def equiv (p : Fin 4) : family flavor scalarFlavor p ≃ₗ[ℂ] ordered flavor scalarFlavor p :=
  MixedSinglePatternAssembly.equiv _ _ _ _

/-- The orbit-supported coefficients really belong to the independent BNV input. -/
theorem family_bnv (p : Fin 4) (f : family flavor scalarFlavor p) :
    f.val ∈ BnvMixedInput.bnvSector flavor scalarFlavor 4 1 := by
  intro labels scalars v w hb
  have hout : ¬ ∃ e : Equiv.Perm (Fin 4), labels ∘ e = pattern p := by
    rintro ⟨e, he⟩
    have hsum : (∑ i, baryon (pattern p i)) = ∑ i, baryon (labels i) := by
      rw [← he]
      exact Equiv.sum_comp e (fun i => baryon (labels i))
    rw [pattern_baryon, hb] at hsum
    norm_num at hsum
  have hw : (fun j => Pi.single (scalars j) (w j)) =
      fun _ : Fin 1 => Pi.single (scalars 0) (w 0) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  change f.val (MixedWeightSupport.pure _ _) = 0
  rw [hw]
  exact f.property labels (scalars 0) v (w 0) (Or.inl hout)

end
end Physics.BnvSevenPatternDescent
