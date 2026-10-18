import Math.RepresentationTheory.GradedSymmetryProtection
import Math.RepresentationTheory.MixedChargeSelection
import Math.RepresentationTheory.CompletenessNaturalityExamples

/-! Exact positive/negative controls for all-degree protection interfaces. -/
namespace Math.SymmetryProtectionExamples
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct BigOperators

/-- Smaller-group restriction remains injective although symmetry enhancement fails. -/
theorem injective_unprotected : Function.Injective
    (InvariantHomRestriction.restrict CompletenessNaturalityExamples.phaseAction
      (⊥ : Subgroup ℂˣ).subtype) ∧
    ¬ InvariantProtection.Protected CompletenessNaturalityExamples.phaseAction
      (⊥ : Subgroup ℂˣ).subtype :=
  ⟨InvariantHomRestriction.injective _ _, fun h =>
    CompletenessNaturalityExamples.restriction_not_surjective
      ((InvariantProtection.protected_iff_surjective _ _).mp h)⟩

abbrev localTrivial := fun _ : Unit => trivial ℂ Unit ℂ
abbrev phase := fun _ : Unit => CompletenessNaturalityExamples.phaseAction
abbrev residualTrivial := fun _ : Unit => trivial ℂ Unit ℂ

/-- One fermion and two bosons: both scalar products and the actual statistics
quotient participate. This proves prohibition on the full mixed input. -/
theorem mixed_one_two_forbidden :
    ∀ f : GradedMixedCompleteness.Input localTrivial localTrivial phase phase 1 2,
      f = 0 := by
  intro f
  apply (GradedMixedCompleteness.equiv localTrivial localTrivial phase phase 1 2).injective
  rw [map_zero]
  funext x
  apply MixedScalarSelection.factor_zero localTrivial localTrivial phase phase
    x.out.1 x.out.2 (-1) (fun _ => -1) (fun _ => -1)
  · intro u v; simp [phase, CompletenessNaturalityExamples.phaseAction]
  · intro u v; simp [phase, CompletenessNaturalityExamples.phaseAction]
  · norm_num [MixedScalarSelection.total, Fin.prod_univ_succ]

/-- A neutral residual representation does not remove the local obstruction. -/
theorem neutral_local_zero (p : Fin 1 → Unit) (s : Fin 0 → Unit)
    (f : IntertwiningMap (TypedMixedSeparatedHom.residual phase phase
      residualTrivial residualTrivial p s) (trivial ℂ Unit ℂ)) : f = 0 := by
  apply MixedScalarSelection.local_factor_zero phase phase residualTrivial residualTrivial p s
    (-1) (-1) (by norm_num)
  have h : ∀ v, TypedMixedSeparatedHom.multiplicityOrdered phase phase p s (-1) v =
      MixedScalarSelection.total p s (fun _ => -1) (fun _ => -1) • v :=
    MixedScalarSelection.ordered_scalar phase phase p s (-1) (fun _ => -1) (fun _ => -1)
      (by intro u v; simp [phase, CompletenessNaturalityExamples.phaseAction])
      (by intro u v; simp [phase, CompletenessNaturalityExamples.phaseAction])
  simpa [TypedMixedSeparatedHom.localOrdered, TypedMixedSeparatedHom.multiplicityOrdered,
    MixedScalarSelection.total, Fin.prod_univ_succ] using h

/-- The charge group can retain B, L and supplied flavor charges simultaneously. -/
theorem charge_vector : MixedChargeSelection.charge
    (fun _ : Unit => ((3 : ℤ), (1 : ℤ), (1 : ℤ)))
    (fun _ : Unit => ((0 : ℤ), (0 : ℤ), (-1 : ℤ)))
    (fun _ : Fin 1 => ()) (fun _ : Fin 1 => ()) = (3,1,0) := by
  simp [MixedChargeSelection.charge]

/-- Cyclic neutrality tests survive conjugate charge cancellation. -/
theorem cyclic_conjugate {k : ℕ} [NeZero k] (q : ZMod k) :
    ¬ ∃ g : CyclicCharge.Group k, MixedChargeSelection.cyclicCharacter g
      (MixedChargeSelection.charge (fun _ : Unit => q) (fun _ : Unit => -q)
        (fun _ : Fin 1 => ()) (fun _ : Fin 1 => ())) ≠ 1 := by
  rw [MixedChargeSelection.cyclic_detect_iff, MixedChargeSelection.conjugate_charge]
  simp
end
end Math.SymmetryProtectionExamples
