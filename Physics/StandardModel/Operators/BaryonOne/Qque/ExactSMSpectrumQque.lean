import Physics.StandardModel.Spectrum.Representations.ExactSMFourWeightTarget
import Physics.StandardModel.Operators.BaryonOne.Qque.LightSMSpeciesQque

open Math

/-! An exact-spectrum adapter with no supplied residual targets or index
conditions. The SM-only spectrum derives both target packages; the retained
two conjugations then give an actual nonzero alternating qque coefficient. -/

namespace Physics.ExactSMSpectrumQque
noncomputable section
open Representation ProductFactorization InvariantWeylMass
open ContinuousRepresentationScope ExactSMResidualSpectrum QqueSpinorExterior

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]

theorem exists_actual_alternation_of_four_weights {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (hd : IsJointlyContinuous D.action)
    (ht : FourWeightLightQque.HasTarget j rho B (target D.action))
    (c : StructuralConjugation.TwoConjugations j) :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation := by
  let := fun i => targetNormedAddCommGroup D.action i
  let := fun i => targetNormedSpace D.action i
  let : Nontrivial (TargetSpace D.action 0) := target_nontrivial D.action hs hn
  have hc : IsJointlyContinuous (secondRestriction D.action) :=
    hd.comp (ContinuousMonoidHom.inr _ H)
  exact LightSMSpeciesQque.exists_actual_alternation j rho B D hu (target D.action)
    hd (target_continuous D.action hc 0) ht (has_species_target j rho B D hs) c

theorem exists_actual_exterior_of_four_weights {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (hd : IsJointlyContinuous D.action)
    (ht : FourWeightLightQque.HasTarget j rho B (target D.action))
    (c : StructuralConjugation.TwoConjugations j) :
    LightSMSpeciesQque.HasActualExterior j rho B D := by
  obtain ⟨fields, hf⟩ := exists_actual_alternation_of_four_weights j rho B D hs hn hu hd ht c
  exact ⟨fields, hf.exists_exterior⟩

/-- Both the weight and species indices are consequences of the exact spectrum. -/
theorem exists_actual_alternation {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (hd : IsJointlyContinuous D.action)
    (c : StructuralConjugation.TwoConjugations j) :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation :=
  exists_actual_alternation_of_four_weights j rho B D hs hn hu hd
    (ExactSMFourWeightTarget.has_target j rho B D hu hs) c

theorem exists_actual_exterior {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (hd : IsJointlyContinuous D.action)
    (c : StructuralConjugation.TwoConjugations j) :
    LightSMSpeciesQque.HasActualExterior j rho B D := by
  obtain ⟨fields, hf⟩ := exists_actual_alternation j rho B D hs hn hu hd c
  exact ⟨fields, hf.exists_exterior⟩

end
end Physics.ExactSMSpectrumQque
