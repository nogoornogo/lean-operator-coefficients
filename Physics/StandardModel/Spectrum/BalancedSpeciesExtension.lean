import Physics.StandardModel.Spectrum.ExactSMAutomaticPositive
import Math.RepresentationTheory.Multiplicity.BalancedMultiplicityExtension

open Math

/-! Positive automatic indices survive balanced residual multiplicity additions.
The exact spectrum is required only of the reference, not the new radical. -/

namespace GUT.BalancedSpeciesExtension
noncomputable section
open Representation ProductFactorization InvariantWeylMass
open ContinuousRepresentationScope ExactSMResidualSpectrum

variable {H G G₀ E E₀ : Type*} [Group H] [Group G] [Group G₀]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  (j : SU5.MaximalTorus.Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (rho.comp (j.prodMap (MonoidHom.id H))))
  (D : LightSMAction.Compatible j rho B)
  (j₀ : SU5.MaximalTorus.Torus →* G₀) (rho₀ : Representation ℂ (G₀ × H) E₀)
  (B₀ : SymmetricMass (rho₀.comp (j₀.prodMap (MonoidHom.id H))))
  (D₀ : LightSMAction.Compatible j₀ rho₀ B₀)

structure Extension where
  quark : BalancedMultiplicityExtension.Extension D.action D₀.action StandardSMGaugeTensor.quark
  up : BalancedMultiplicityExtension.Extension D.action D₀.action StandardSMGaugeTensor.upRight.dual
  electron : BalancedMultiplicityExtension.Extension D.action D₀.action
    StandardSMGaugeTensor.electronRight.dual

def refl : Extension j rho B D j rho B D where
  quark := BalancedMultiplicityExtension.refl D.action _
  up := BalancedMultiplicityExtension.refl D.action _
  electron := BalancedMultiplicityExtension.refl D.action _

omit [FiniteDimensional ℂ E] in
/-- Nonzero paired Q additions are not hidden inside the old exact spectrum. -/
theorem not_exact_of_quark_extra
    (ext : Extension j rho B D j₀ rho₀ B₀ D₀) (hp : 0 < ext.quark.dimension)
    (n s : ℕ) : ¬ ExactSMSpectrum.HasSpectrum (firstRestriction D.action) n s := by
  intro hs
  have hz := (ExactSMSpectrum.exact_opposite_multiplicities hs).1
  change Module.finrank ℂ
    (MultiplicitySpace D.action StandardSMGaugeTensor.quark.dual) = 0 at hz
  have he := BalancedMultiplicityExtension.negative_finrank _ _ _ ext.quark
  omega

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  (hd : IsJointlyContinuous D.action)

theorem shared_positive
    (ext : Extension j rho B D j₀ rho₀ B₀ D₀) {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D₀.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho₀.comp (j₀.prodMap (MonoidHom.id H)))))
    (c : StructuralConjugation.TwoConjugations j₀) :
    SharedPositiveSpeciesIndex.SharedPositive
      (AutomaticSMSpeciesIndex.coefficients j rho B D hd) := by
  let F := AutomaticSMSpeciesIndex.presentation j rho B D hd
  let := fun i => targetNormedAddCommGroup D₀.action i
  let := fun i => targetNormedSpace D₀.action i
  let : Nontrivial (TargetSpace D₀.action 0) := target_nontrivial D₀.action hs hn
  have ht := ExactSMFourWeightTarget.has_target j₀ rho₀ B₀ D₀ hu hs
  have he := FourWeightLightQque.characters_compatible j₀ rho₀ B₀ hu
    (target D₀.action) ht c
  have hq (h : H) : (target D₀.action 0).character h =
      CompactVirtualCharacter.character F.action (F.coefficients 0) h :=
    (species_indices D₀.action hs h).1.symm.trans
      ((BalancedMultiplicityExtension.index_eq _ _ _ ext.quark h).symm.trans (F.character 0 h))
  have hu' (h : H) : (target D₀.action 1).character h =
      CompactVirtualCharacter.character F.action (F.coefficients 1) h :=
    (species_indices D₀.action hs h).2.1.symm.trans
      ((BalancedMultiplicityExtension.index_eq _ _ _ ext.up h).symm.trans (F.character 1 h))
  have he' (h : H) : (target D₀.action 4).character h =
      CompactVirtualCharacter.character F.action (F.coefficients 4) h :=
    (species_indices D₀.action hs h).2.2.symm.trans
      ((BalancedMultiplicityExtension.index_eq _ _ _ ext.electron h).symm.trans (F.character 4 h))
  apply SharedPositiveSpeciesIndex.of_common_index F.action F.coefficients
    F.continuous F.inequivalent
  · exact ⟨funext fun h => (hq h).symm.trans ((congrFun he.1 h).trans (hu' h)),
      funext fun h => (hq h).symm.trans ((congrFun he.2 h).trans (he' h))⟩
  · exact CompactVirtualCharacter.dimension_pos_of_actual F.action (F.coefficients 0)
      (target D₀.action 0) hq

theorem pairwise_positive
    (ext : Extension j rho B D j₀ rho₀ B₀ D₀) {n s : ℕ}
    (hs : ExactSMSpectrum.HasSpectrum (firstRestriction D₀.action) n s) (hn : 0 < n)
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation
      (ResidualWeightSpace.torus (rho₀.comp (j₀.prodMap (MonoidHom.id H)))))
    (c : StructuralConjugation.TwoConjugations j₀) :
    AutomaticSMSpeciesIndex.PairwisePositive j rho B D hd :=
  PairwisePositiveSpeciesIndex.of_shared
    (shared_positive j rho B D j₀ rho₀ B₀ D₀ hd ext hs hn hu c)

end
end GUT.BalancedSpeciesExtension
