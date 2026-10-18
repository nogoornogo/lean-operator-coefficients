import Physics.StandardModel.Spectrum.LeptonTrialitySpectrum
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Closed actual-source counterexample: no UV application import, no extra
axioms, and actual nonzero vectors in the mass radical. -/

set_option autoImplicit false

namespace GUT.LeptonTrialitySpectrum.Audit

open LeptonTriality LeptonTrialitySource
open StandardSMCharacterTarget FiniteAbelianChargeSectors

example : actualSpectrum = LeptonTriality.spectrum := actualSpectrum_eq

example : StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
    actualSpectrum := actual_forbids_all_supported

example (i : Fin 15) :
    ∃ v : restrictedMass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, restrictedMass.radical.toRepresentation g v =
        keyCharacter (smResolvedKey assignment i) g • v := exists_joint_zeroMode i

example (g : LeptonTrialitySource.Group) (v w : HilbertMatter) :
    mass.form (rho g v) (rho g w) = mass.form v w := mass.invariant g v w

end GUT.LeptonTrialitySpectrum.Audit

run_cmd do
  -- Current source layers are the boundary here. Historical namespaces of
  -- shared coordinate lemmas are preserved and reported for diagnostics.
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Triality spectrum imports UV application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.SU5.PhysicalTorus.gaugeHom,
    ``GUT.SU5.PhysicalTorus.toTorus_surjective,
    ``GUT.SU5.TorusCharacter.keyCharacter_injective,
    ``GUT.LeptonTrialitySpectrum.keyCharacter_injective,
    ``GUT.LeptonTrialitySpectrum.eval_lift,
    ``GUT.LeptonTrialitySpectrum.eval_target_sum,
    ``GUT.LeptonTrialitySpectrum.trace_target,
    ``GUT.LeptonTrialitySpectrum.restricted_unitary,
    ``GUT.LeptonTrialitySpectrum.restrictedMass,
    ``GUT.LeptonTrialitySpectrum.radical_trace,
    ``GUT.LeptonTrialitySpectrum.full_spectrum_eq,
    ``GUT.LeptonTrialitySpectrum.actualSpectrum_eq,
    ``GUT.LeptonTrialitySpectrum.actual_chiral_index,
    ``GUT.LeptonTrialitySpectrum.radical_dual_trace,
    ``GUT.LeptonTrialitySpectrum.actual_forbids_all_supported,
    ``GUT.LeptonTrialitySpectrum.actual_supported,
    ``GUT.LeptonTrialitySpectrum.actual_not_weylInvariant,
    ``GUT.LeptonTrialitySpectrum.exists_joint_zeroMode,
    ``GUT.LeptonTrialitySpectrum.actual_source_counterexample]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Triality spectrum: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Triality spectrum: import boundary and {declarations.length} strict transitive axiom checks passed"
