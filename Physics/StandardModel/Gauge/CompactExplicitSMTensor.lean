import Physics.StandardModel.Gauge.ExplicitSMResidualTensor
import Physics.StandardModel.Gauge.PhysicalTorus
import Physics.StandardModel.Operators.CompactLightQque

open Math

/-! The compact residual coefficient on actual weight spaces lifts to an
ordered full-SM x H coefficient when explicit compatible SM field decompositions
are supplied. The decomposition is an additional hypothesis, not derived here. -/

namespace GUT.CompactExplicitSMTensor
set_option autoImplicit false
noncomputable section

open Representation InvariantWeylMass NonabelianLightSource
open ExternalInvariantTensor ContinuousRepresentationScope
open SU5.MaximalTorus

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))

/-- Full gauge data on the unchanged radical, with agreement on the physical
covering torus. Q is left-chiral; right-handed fields lie in the dual radical.
No invariant qque coefficient or mass interaction is included in this input. -/
structure Decomposition where
  action : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) B.radical.toSubmodule
  restriction : action.comp (SU5.PhysicalTorus.gaugeHom.prodMap (MonoidHom.id H)) =
    B.radical.toRepresentation.comp (SU5.PhysicalTorus.toTorus.prodMap (MonoidHom.id H))
  quark : Subrepresentation action
  upRight : Subrepresentation action.dual
  electronRight : Subrepresentation action.dual
  quark0 : Representation.Equiv quark.toRepresentation
    (external StandardSMGaugeTensor.quark (lightSector j rho B 0))
  quark3 : Representation.Equiv quark.toRepresentation
    (external StandardSMGaugeTensor.quark (lightSector j rho B 3))
  up8 : Representation.Equiv upRight.toRepresentation
    (external StandardSMGaugeTensor.upRight (lightSector j rho B 8).dual)
  electron14 : Representation.Equiv electronRight.toRepresentation
    (external StandardSMGaugeTensor.electronRight (lightSector j rho B 14).dual)

abbrev fieldTensor (D : Decomposition j rho B) :=
  (D.quark.toRepresentation.tprod D.quark.toRepresentation).tprod
    (D.upRight.toRepresentation.tprod D.electronRight.toRepresentation)

omit [FiniteDimensional ℂ E] in
/-- The covering-torus compatibility includes the original residual H action. -/
theorem residual_agrees (D : Decomposition j rho B) (h : H) :
    D.action (1, h) = B.radical.toRepresentation (1, h) := by
  have he := DFunLike.congr_fun D.restriction (1, h)
  simpa using he

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {F : Fin 5 → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℂ (F s)]
  [FiniteDimensional ℂ (F 0)] [Nontrivial (F 0)]

set_option maxHeartbeats 4000000 in
theorem exists_qque
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (P : ∀ s, Representation ℂ H (F s))
    (hr : IsJointlyContinuous (rho.comp (MonoidHom.inr G H)))
    (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (c : StructuralConjugation.TwoConjugations j)
    (D : Decomposition j rho B) :
    ∃ f : IntertwiningMap (fieldTensor j rho B D)
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) ℂ), f ≠ 0 := by
  obtain ⟨f, hf⟩ := CompactLightQque.exists_qque_coefficient j rho B hu P hr hp ht c
  exact ExplicitSMResidualTensor.exists_on_fields
    (lightSector j rho B 0) (lightSector j rho B 3)
    (lightSector j rho B 8).dual (lightSector j rho B 14).dual
    D.quark.toRepresentation D.upRight.toRepresentation D.electronRight.toRepresentation
    D.quark0 D.quark3 D.up8 D.electron14 f hf

end
end GUT.CompactExplicitSMTensor
