import Physics.StandardModel.Spectrum.AutomaticSMSpeciesIndex
import Physics.StandardModel.Spectrum.ExactSMFourWeightTarget

open Math

/-! The exact-spectrum entrance also supplies the positive-constituent test
for the automatically constructed normalized species presentation. -/

namespace GUT.ExactSMAutomaticPositive
noncomputable section
open Representation InvariantWeylMass ContinuousRepresentationScope ProductFactorization
open ExactSMResidualSpectrum

variable {H G E : Type*} [Group H] [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (hd : IsJointlyContinuous D.action)

theorem shared_positive {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (c : StructuralConjugation.TwoConjugations j) :
    SharedPositiveSpeciesIndex.SharedPositive
      (AutomaticSMSpeciesIndex.coefficients j rho B D hd) := by
  let F := AutomaticSMSpeciesIndex.presentation j rho B D hd
  let := fun i => targetNormedAddCommGroup D.action i
  let := fun i => targetNormedSpace D.action i
  let : Nontrivial (TargetSpace D.action 0) := target_nontrivial D.action hs hn
  have ht := ExactSMFourWeightTarget.has_target j rho B D hu hs
  have he := FourWeightLightQque.characters_compatible j rho B hu (target D.action) ht c
  have hq (h : H) : (target D.action 0).character h =
      CompactVirtualCharacter.character F.action (F.coefficients 0) h :=
    (species_indices D.action hs h).1.symm.trans (F.character 0 h)
  have hu' (h : H) : (target D.action 1).character h =
      CompactVirtualCharacter.character F.action (F.coefficients 1) h :=
    (species_indices D.action hs h).2.1.symm.trans (F.character 1 h)
  have he' (h : H) : (target D.action 4).character h =
      CompactVirtualCharacter.character F.action (F.coefficients 4) h :=
    (species_indices D.action hs h).2.2.symm.trans (F.character 4 h)
  apply SharedPositiveSpeciesIndex.of_common_index F.action F.coefficients
    F.continuous F.inequivalent
  · exact ⟨funext fun h => (hq h).symm.trans ((congrFun he.1 h).trans (hu' h)),
      funext fun h => (hq h).symm.trans ((congrFun he.2 h).trans (he' h))⟩
  · exact CompactVirtualCharacter.dimension_pos_of_actual F.action (F.coefficients 0)
      (target D.action 0) hq

theorem pairwise_positive {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho.comp (j.prodMap (MonoidHom.id H)))))
    (c : StructuralConjugation.TwoConjugations j) :
    AutomaticSMSpeciesIndex.PairwisePositive j rho B D hd :=
  PairwisePositiveSpeciesIndex.of_shared (shared_positive j rho B D hd hs hn hu c)

end
end GUT.ExactSMAutomaticPositive
