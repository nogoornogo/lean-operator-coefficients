import Physics.StandardModel.Spectrum.Mass.LightSMSpeciesIndex
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior
import Physics.StandardModel.Gauge.Tensors.LightSMFieldExtraction

open Math

/-! Exterior qque on canonical multiplicity models and on actual invariant
subspaces of the original light radical and its algebraic dual. -/

namespace Physics.LightSMSpeciesQque
set_option autoImplicit false
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open SU5.MaximalTorus QqueSpinorExterior

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  {F : Fin 5 → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, NormedSpace ℂ (F s)]
  [FiniteDimensional ℂ (F 0)] [Nontrivial (F 0)]

theorem exists_model_exterior
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (P : ∀ s, Representation ℂ H (F s))
    (hd : IsJointlyContinuous D.action) (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (hs : LightSMSpeciesIndex.HasTarget j rho B D P)
    (c : StructuralConjugation.TwoConjugations j) :
    HasModelExterior
      (a := LightSMSpeciesIndex.quark j rho B D)
      (b := LightSMSpeciesIndex.up j rho B D)
      (d := LightSMSpeciesIndex.electron j rho B D) := by
  obtain ⟨S, _, hn, ⟨sq⟩, ⟨su⟩, ⟨se⟩⟩ :=
    LightSMSpeciesIndex.common_quotient j rho B D P hu hd hp ht hs c
  let : Nontrivial S.toSubmodule := hn
  exact hasModelExterior sq su se

/-- The actual-field endpoint includes the source-derived identifications.
In particular, neither an SM decomposition nor a splitting is an input. -/
def HasActualExterior : Prop :=
  ∃ fields : LightSMFieldExtraction.Fields D.action,
    ∃ f : ExteriorCoefficient fields.Q.toRepresentation fields.U.toRepresentation
      fields.E.toRepresentation, f ≠ 0

theorem exists_actual_alternation
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (P : ∀ s, Representation ℂ H (F s))
    (hd : IsJointlyContinuous D.action) (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (hs : LightSMSpeciesIndex.HasTarget j rho B D P)
    (c : StructuralConjugation.TwoConjugations j) :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation := by
  let : MeasurableSpace (StandardSMGaugeTensor.GaugeGroup × H) := borel _
  let : BorelSpace (StandardSMGaugeTensor.GaugeGroup × H) := ⟨rfl⟩
  obtain ⟨fields⟩ := LightSMFieldExtraction.nonempty_fields D.action
    (CompactIrreducibleQuotient.semisimple D.action hd)
  obtain ⟨S, _, hn, ⟨sq⟩, ⟨su⟩, ⟨se⟩⟩ :=
    LightSMSpeciesIndex.common_quotient j rho B D P hu hd hp ht hs c
  let : Nontrivial S.toSubmodule := hn
  exact ⟨fields, exists_on_fields sq su se
    fields.Q.toRepresentation fields.U.toRepresentation fields.E.toRepresentation
    fields.quarkEquiv fields.upEquiv fields.electronEquiv⟩

theorem exists_actual_exterior
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (P : ∀ s, Representation ℂ H (F s))
    (hd : IsJointlyContinuous D.action) (hp : IsJointlyContinuous (P 0))
    (ht : FourWeightLightQque.HasTarget j rho B P)
    (hs : LightSMSpeciesIndex.HasTarget j rho B D P)
    (c : StructuralConjugation.TwoConjugations j) :
    HasActualExterior j rho B D := by
  obtain ⟨fields, hf⟩ := exists_actual_alternation j rho B D hu P hd hp ht hs c
  exact ⟨fields, hf.exists_exterior⟩

end
end Physics.LightSMSpeciesQque
