import Physics.StandardModel.Spectrum.AutomaticSMSpeciesIndex
import Physics.StandardModel.Operators.PairwisePositiveQque

open Math

/-! Qque from positive support of the automatically constructed actual indices.
Normalization and matching certificates are derived, not supplied. -/

namespace GUT.AutomaticSpeciesQque
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope
open SU5.MaximalTorus QqueSpinorExterior

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (hd : IsJointlyContinuous D.action)

theorem exists_actual_alternation (hp : AutomaticSMSpeciesIndex.PairwisePositive j rho B D hd) :
    ∃ fields : LightSMFieldExtraction.Fields D.action,
      HasNonzeroAlternation fields.Q.toRepresentation fields.U.toRepresentation
        fields.E.toRepresentation :=
  PairwisePositiveQque.exists_actual_alternation j rho B D
    (AutomaticSMSpeciesIndex.action j rho B D hd)
    (AutomaticSMSpeciesIndex.coefficients j rho B D hd)
    (AutomaticSMSpeciesIndex.continuous j rho B D hd)
    (AutomaticSMSpeciesIndex.inequivalent j rho B D hd) hd
    (AutomaticSMSpeciesIndex.species_matches j rho B D hd) hp

theorem exists_actual_exterior (hp : AutomaticSMSpeciesIndex.PairwisePositive j rho B D hd) :
    LightSMSpeciesQque.HasActualExterior j rho B D := by
  obtain ⟨fields, hf⟩ := exists_actual_alternation j rho B D hd hp
  exact ⟨fields, hf.exists_exterior⟩

end
end GUT.AutomaticSpeciesQque
