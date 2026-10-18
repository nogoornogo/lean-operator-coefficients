import Physics.StandardModel.Spectrum.FourWeightQque
import Physics.StandardModel.Spectrum.ConjugationTrialityObstruction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace GUT.FourWeightControls
noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open FiniteChargeProfiles QqueLocalTarget

def neutralProfiles : Profiles ℤ :=
  ⟨Finsupp.single 0 1, Finsupp.single 0 1, 0, 0, Finsupp.single 0 1⟩

def spectatorProfiles : Profiles ℤ :=
  { neutralProfiles with down := Finsupp.single 0 1 }

/-- A profile-level strictness control, not an actual ambient model example. -/
theorem four_target_not_fifteen :
    Matches (targetWithSinglets neutralProfiles 0) spectatorProfiles ∧
    ¬ SMPartialTarget.MatchesSM (targetWithSinglets neutralProfiles 0) spectatorProfiles ∧
    0 < total spectatorProfiles.quark := by
  refine ⟨?_, ?_, ?_⟩
  · apply (matches_iff_of_profiles_eq _ neutralProfiles spectatorProfiles rfl rfl rfl).mp
    exact of_matchesSM _ _ (SMPartialTarget.of_full_target _ _ 0 rfl)
  · intro ht
    have he := ht 9 0
    rw [chiralDifference_target_apply] at he
    change (0 : ℤ) = ((Finsupp.single (0 : ℤ) 1 : ℤ →₀ ℕ) 0 : ℤ) at he
    norm_num at he
  · simp [spectatorProfiles, neutralProfiles]

/-- A positive target cannot be supplied by a zero spectrum. -/
theorem zero_spectrum_not_positive_target : ¬ Matches 0 neutralProfiles := by
  intro ht
  have he := ht 0 (Or.inl rfl) 0
  norm_num [chiralDifference, dualCharacter_apply, neutralProfiles, smCharge] at he

open SU5.MaximalTorus StructuralConjugation InvariantWeylMass

/-- Even four-weight matching excludes the earlier triality counterexample. -/
theorem triality_no_two {G E : Type*} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j : Torus →* G) (rho : Representation ℂ (G × LeptonTriality.Residual) E)
    (B : SymmetricMass (restrict j rho))
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
    (ht : FourWeightQque.HasTarget j rho B hu LeptonTriality.family.profiles) :
    ¬ Nonempty (TwoConjugations j) := by
  rintro ⟨c⟩
  have he := congrArg (fun p => p 0)
    (FourWeightQque.quark_profiles_compatible j rho B hu LeptonTriality.family.profiles c ht).2
  norm_num [LeptonTriality.family, FiniteChargeProfiles.pure,
    LeptonTriality.assignment, LeptonTriality.charges,
    LeptonTriality.label_ne_zero] at he

end
end GUT.FourWeightControls

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Four-weight qque imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.QqueLocalTarget.of_matchesSM,
    ``GUT.QqueLocalTarget.profile_eq,
    ``GUT.QqueLocalTarget.coefficient_lower_bound,
    ``GUT.QqueLocalTarget.matches_iff_of_profiles_eq,
    ``GUT.QqueLocalTarget.add_of_dual_vanishes,
    ``GUT.FourWeightQque.of_partial_target,
    ``GUT.FourWeightQque.quark_profiles_compatible,
    ``GUT.FourWeightQque.exists_zeroMode,
    ``GUT.FourWeightQque.exists_supported_qque,
    ``GUT.FourWeightQque.slotwise_selection_rule_obstruction,
    ``GUT.FourWeightControls.four_target_not_fifteen,
    ``GUT.FourWeightControls.zero_spectrum_not_positive_target,
    ``GUT.FourWeightControls.triality_no_two]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Four-weight qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Four-weight qque: layer and {declarations.length} strict axiom checks passed"
