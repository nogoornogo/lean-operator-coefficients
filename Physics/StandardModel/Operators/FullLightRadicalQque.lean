import Physics.StandardModel.Operators.FullLightSpeciesQque
import Physics.StandardModel.Gauge.LightSMAction

open Math

/-! Necessary and sufficient qque selection rules on all standard species of
the unchanged mass radical. No positive-support or conjugation premise. -/
namespace GUT.FullLightRadicalQque
noncomputable section
open Representation ProductFactorization InvariantWeylMass
open ContinuousRepresentationScope StandardSMGaugeTensor

variable {H G V : Type*} [Group H] [Group G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) V)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)

/-- Only the SM restriction needs analytic structure for this adapter. -/
theorem sm_semisimple
    (hd : IsJointlyContinuous (firstRestriction D.action)) :
    IsSemisimpleRepresentation (firstRestriction D.action) := by
  let : MeasurableSpace GaugeGroup := borel GaugeGroup
  let : BorelSpace GaugeGroup := ⟨rfl⟩
  exact CompactIrreducibleQuotient.semisimple (firstRestriction D.action) hd

def equiv (hd : IsJointlyContinuous (firstRestriction D.action)) :
    FullLightSpeciesQque.ResidualHom D.action ≃ₗ[ℂ]
      FullLightSpeciesQque.Sector D.action :=
  FullLightSpeciesQque.equiv D.action (sm_semisimple j rho B D hd)

theorem nonzero_iff (hd : IsJointlyContinuous (firstRestriction D.action)) :
    FullLightSpeciesQque.HasCoefficient D.action ↔
      FullLightSpeciesQque.HasResidualMap D.action :=
  FullLightSpeciesQque.nonzero_iff D.action (sm_semisimple j rho B D hd)

theorem all_forbidden_iff (hd : IsJointlyContinuous (firstRestriction D.action)) :
    ¬ FullLightSpeciesQque.HasCoefficient D.action ↔
      ¬ FullLightSpeciesQque.HasResidualMap D.action :=
  not_congr (nonzero_iff j rho B D hd)

variable [TopologicalSpace H]

theorem nonzero_iff_of_jointlyContinuous (hd : IsJointlyContinuous D.action) :
    FullLightSpeciesQque.HasCoefficient D.action ↔
      FullLightSpeciesQque.HasResidualMap D.action :=
  nonzero_iff j rho B D (hd.comp (ContinuousMonoidHom.inl GaugeGroup H))

theorem all_forbidden_iff_of_jointlyContinuous (hd : IsJointlyContinuous D.action) :
    ¬ FullLightSpeciesQque.HasCoefficient D.action ↔
      ¬ FullLightSpeciesQque.HasResidualMap D.action :=
  all_forbidden_iff j rho B D (hd.comp (ContinuousMonoidHom.inl GaugeGroup H))

end
end GUT.FullLightRadicalQque
