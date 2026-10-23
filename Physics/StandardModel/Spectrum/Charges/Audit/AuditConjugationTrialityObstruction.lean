import Physics.StandardModel.Spectrum.Charges.ConjugationTrialityObstruction
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Negative control against the actual, nonempty triality mass source. -/

set_option autoImplicit false

namespace Physics.StructuralConjugationTriality.Audit

open SU5 SU5.MaximalTorus StructuralConjugation LeptonTriality

example : Module.finrank ℂ LeptonTrialitySource.mass.radical.toSubmodule = 45 ∧
    StandardAbelianCharge.ChargesSupported LeptonTrialitySpectrum.actualSpectrum assignment ∧
    StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      LeptonTrialitySpectrum.actualSpectrum :=
  ⟨LeptonTrialitySource.radical_finrank, LeptonTrialitySpectrum.actual_supported,
    LeptonTrialitySpectrum.actual_forbids_all_supported⟩

example {G : Type*} [Group G] (j : Torus →* G)
    (rho : Representation ℂ (G × Residual) LeptonTrialitySource.HilbertMatter)
    (ha : ∀ z h, (restrict j rho) (PhysicalTorus.toTorus z, h) =
      LeptonTrialitySpectrum.restricted (z, h)) :
    ¬ Nonempty (ThreeConjugations j) := no_actual_extension j rho ha

end Physics.StructuralConjugationTriality.Audit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Conjugation triality imports UV application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.StructuralConjugationTriality.family_not_compatible,
    ``Physics.StructuralConjugationTriality.target_with_zero,
    ``Physics.StructuralConjugationTriality.no_conjugations_of_dual_target,
    ``Physics.StructuralConjugationTriality.no_conjugations_of_light_target,
    ``Physics.StructuralConjugationTriality.actual_source_trace,
    ``Physics.StructuralConjugationTriality.no_conjugations_of_actual_source_character,
    ``Physics.StructuralConjugationTriality.no_actual_extension]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conjugation triality: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conjugation triality: import boundary and {declarations.length} strict transitive axiom checks passed"
