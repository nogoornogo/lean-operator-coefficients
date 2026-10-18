import Physics.StandardModel.Spectrum.TwoConjugationQque
import Physics.StandardModel.Spectrum.ConjugationTrialityObstruction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace GUT.TwoConjugationControls

open SU5.MaximalTorus StructuralConjugation InvariantWeylMass

/-- The existing light triality target still excludes the weakened criterion. -/
theorem triality_no_two {G E : Type*} [Group G] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j : Torus →* G) (rho : Representation ℂ (G × LeptonTriality.Residual) E)
    (B : SymmetricMass (restrict j rho))
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
    (ht : ConjugationPartialTarget.HasPartialTarget j rho B hu LeptonTriality.family.profiles) :
    ¬ Nonempty (TwoConjugations j) := by
  rintro ⟨c⟩
  exact StructuralConjugationTriality.family_not_compatible
    (TwoConjugationQque.profiles_compatible j rho B hu LeptonTriality.family.profiles c ht)

end GUT.TwoConjugationControls

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Two conjugations imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.StructuralConjugation.ThreeConjugations.toTwo,
    ``GUT.StructuralConjugation.swap31_down_lepton,
    ``GUT.TwoConjugationQque.quark_profiles_compatible,
    ``GUT.TwoConjugationQque.exists_common_charge,
    ``GUT.TwoConjugationQque.profiles_compatible,
    ``GUT.TwoConjugationQque.qqueCharges_neutral,
    ``GUT.TwoConjugationQque.exists_supported_qque,
    ``GUT.TwoConjugationQque.slotwise_selection_rule_obstruction,
    ``GUT.TwoConjugationQque.legacy_selection_rule_obstruction,
    ``GUT.TwoConjugationQque.exists_actual_signature_pair,
    ``GUT.TwoConjugationQque.selection_rule_obstruction,
    ``GUT.TwoConjugationControls.triality_no_two]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Two conjugations: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Two conjugations: layer and {declarations.length} strict axiom checks passed"
