import Math.RepresentationTheory.Protection.ComposableProtection
import Math.RepresentationTheory.Protection.SymmetryProtectionExamples

namespace Math.ComposableProtectionExamples
set_option autoImplicit false
noncomputable section
open Representation ProhibitionSpecification SymmetryProtectionExamples

theorem overlapping (s : Spec Unit Unit) (n m : ℕ) (p : Fin n → Unit) (q : Fin m → Unit) :
    (union s s).test n m p q ↔ s.test n m p q := by
  simp [union]

/-- The supplied phase action kills any selected support at degree (1,2). -/
theorem selected_phase (s : Spec Unit Unit) :
    ∀ f : MixedSpeciesProjection.supportSpace (s.test 1 2)
      (TypedMixedSeparatedHom.fieldF localTrivial phase)
      (TypedMixedSeparatedHom.fieldB localTrivial phase), f = 0 := by
  rw [ComposableProtection.forbidden_iff localTrivial localTrivial phase phase s 1 2]
  intro x _ q
  apply MixedScalarSelection.factor_zero localTrivial localTrivial phase phase
    x.out.1 x.out.2 (-1) (fun _ => -1) (fun _ => -1)
  · intro u v; simp [phase, CompletenessNaturalityExamples.phaseAction]
  · intro u v; simp [phase, CompletenessNaturalityExamples.phaseAction]
  · norm_num [MixedScalarSelection.total, Fin.prod_univ_succ]

/-- Charge-neutral contents may still fail local invariance. -/
theorem neutral_local (p : Fin 1 → Unit) (q : Fin 0 → Unit) :
    ∀ f : IntertwiningMap (TypedMixedSeparatedHom.residual phase phase
      residualTrivial residualTrivial p q) (trivial ℂ Unit ℂ), f = 0 := by
  intro f
  exact neutral_local_zero _ _ f
end
end Math.ComposableProtectionExamples
