import Physics.StandardModel.Gauge.Tensors.CompactExplicitSMTensor
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior

open Math

/-! Nonzero alternating qque coefficients on actual light fields with spinors.
The full-SM decomposition remains an explicit input, exactly as in the
ordered internal endpoint. No generation or coupling nonzero assumption. -/

namespace Physics.CompactLightExteriorQque
set_option autoImplicit false
noncomputable section
open Representation InvariantWeylMass NonabelianLightSource
open ContinuousRepresentationScope
open SU5.MaximalTorus

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {F : Fin 5 → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℂ (F s)]
  [FiniteDimensional ℂ (F 0)] [Nontrivial (F 0)]

set_option maxHeartbeats 400000 in
theorem exists_ordered_nonzero_exterior
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (P : ∀ s, Representation ℂ H (F s))
    (hr : IsJointlyContinuous (rho.comp (MonoidHom.inr G H)))
    (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (c : StructuralConjugation.TwoConjugations j)
    (D : CompactExplicitSMTensor.Decomposition j rho B) :
    QqueSpinorExterior.HasNonzeroAlternation D.quark.toRepresentation
      D.upRight.toRepresentation D.electronRight.toRepresentation := by
  obtain ⟨S, _, hn, hs⟩ := CompactLightQque.common_quotient j rho B hu P hr hp ht c
  let : Nontrivial S.toSubmodule := hn
  obtain ⟨sq⟩ := hs 0 (Or.inl rfl)
  obtain ⟨su⟩ := hs 8 (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨se⟩ := hs 14 (Or.inr (Or.inr (Or.inr rfl)))
  exact QqueSpinorExterior.exists_on_fields sq su se
    D.quark.toRepresentation D.upRight.toRepresentation D.electronRight.toRepresentation
    D.quark0 D.up8 D.electron14

theorem exists_qque
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (P : ∀ s, Representation ℂ H (F s))
    (hr : IsJointlyContinuous (rho.comp (MonoidHom.inr G H)))
    (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (c : StructuralConjugation.TwoConjugations j)
    (D : CompactExplicitSMTensor.Decomposition j rho B) :
    ∃ f : QqueSpinorExterior.ExteriorCoefficient D.quark.toRepresentation
      D.upRight.toRepresentation D.electronRight.toRepresentation, f ≠ 0 :=
  QqueSpinorExterior.HasNonzeroAlternation.exists_exterior _ _ _
    (exists_ordered_nonzero_exterior j rho B hu P hr hp ht c D)

end
end Physics.CompactLightExteriorQque
