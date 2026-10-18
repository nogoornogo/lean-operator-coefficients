import GUT.Common.StandardChain.StandardChain
import Physics.StandardModel.Spectrum.ConjugationMassSource

open Math

/-! Construct the three actual conjugations for every supplied SU(5) chain.
The new endpoint uses precisely the old matter, mass and resolved spectrum. -/

set_option autoImplicit false

namespace GUT.StandardChainConjugation

noncomputable section
open SU5 StandardModelEmbedding StructuralConjugation StandardChain
open FiniteAbelianChargeSectors InvariantWeylMass StandardModelLocalOperator
open StandardSMCharacterTarget

variable {G : Type*} [Group G]

def realizes (i : TargetGroup →* G) (p : Equiv.Perm (Fin 5)) :
    Realizes (i.comp MaximalTorus.hom) p where
  element := i (MonomialElements.signedPermutation p)
  conjugate t := by
    change i (MaximalTorus.hom (MaximalTorus.permute p t)) = _
    rw [MaximalTorus.hom_conjugate, map_mul, map_mul, map_inv]
    rfl

def threeConjugations (i : TargetGroup →* G) : ThreeConjugations (i.comp MaximalTorus.hom) where
  quarkUp := realizes i (Equiv.swap (3 : Fin 5) 1)
  quarkElectron := realizes i (Equiv.swap (0 : Fin 5) 4)
  downLepton := realizes i (Equiv.swap (0 : Fin 5) 3)

variable {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
theorem restrict_eq (i : TargetGroup →* G) (rho : Representation ℂ (G × H) E) :
    StructuralConjugation.restrict (i.comp MaximalTorus.hom) rho =
      TorusCharacterSource.restrict (pullback i rho) := rfl

variable {i : TargetGroup →* G} {rho : Representation ℂ (G × H) E} (M : Model i rho)

def mass : SymmetricMass (StructuralConjugation.restrict (i.comp MaximalTorus.hom) rho) :=
  M.mass

omit [FiniteDimensional ℂ E] in
@[simp] theorem mass_eq : mass M = M.mass := rfl

omit [FiniteDimensional ℂ E] in
theorem hasTarget : StructuralConjugationMass.HasTarget (i.comp MaximalTorus.hom)
    rho (mass M) M.profile.profiles M.singlets := M.lightTarget

theorem spectrum_eq :
    StructuralConjugationMass.spectrum (i.comp MaximalTorus.hom) rho M.unitary (mass M) =
      M.lightSpectrum := rfl

theorem profiles_compatible : FiniteChargeProfiles.OrbitCompatible M.profile.profiles :=
  StructuralConjugationMass.profiles_compatible (i.comp MaximalTorus.hom) rho
    (mass M) _ _ (threeConjugations i) (hasTarget M)

theorem actual_signature_pair :
    ∃ Q D : SupportedInvariantOperator M.lightSpectrum,
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ k : Fin 15, ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, M.mass.radical.toRepresentation g v =
          TorusCharacter.keyCharacter (smResolvedKey Q.charges k) g • v := by
  exact StructuralConjugationMass.exists_actual_signature_pair (i.comp MaximalTorus.hom)
      rho M.unitary (mass M) M.singlets M.profile (threeConjugations i) (hasTarget M)

theorem selection_rule_obstruction :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator M.lightSpectrum := by
  rw [← spectrum_eq M]
  exact StructuralConjugationMass.selection_rule_obstruction (i.comp MaximalTorus.hom)
    rho M.unitary (mass M) M.singlets M.profile (threeConjugations i) (hasTarget M)

section Continuous
variable [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace H] [IsTopologicalGroup H]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The same continuous model is consumed; no replacement action or topology. -/
theorem continuous_selection_rule_obstruction (N : ContinuousModel i rho) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator N.toModel.lightSpectrum :=
  selection_rule_obstruction N.toModel

end Continuous

end
end GUT.StandardChainConjugation
