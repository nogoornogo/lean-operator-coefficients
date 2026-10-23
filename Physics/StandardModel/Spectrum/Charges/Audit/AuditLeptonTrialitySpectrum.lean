import Physics.StandardModel.Spectrum.Charges.LeptonTrialitySpectrum
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Closed actual-source counterexample: no UV application import, no extra
axioms, and actual nonzero vectors in the mass radical. -/

set_option autoImplicit false

namespace Physics.LeptonTrialitySpectrum.Audit

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

end Physics.LeptonTrialitySpectrum.Audit

run_cmd do
  -- Current source layers are the boundary here. Historical namespaces of
  -- shared coordinate lemmas are preserved and reported for diagnostics.
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Triality spectrum imports UV application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.SU5.PhysicalTorus.gaugeHom,
    ``Physics.SU5.PhysicalTorus.toTorus_surjective,
    ``Physics.SU5.TorusCharacter.keyCharacter_injective,
    ``Physics.LeptonTrialitySpectrum.keyCharacter_injective,
    ``Physics.LeptonTrialitySpectrum.eval_lift,
    ``Physics.LeptonTrialitySpectrum.eval_target_sum,
    ``Physics.LeptonTrialitySpectrum.trace_target,
    ``Physics.LeptonTrialitySpectrum.restricted_unitary,
    ``Physics.LeptonTrialitySpectrum.restrictedMass,
    ``Physics.LeptonTrialitySpectrum.radical_trace,
    ``Physics.LeptonTrialitySpectrum.full_spectrum_eq,
    ``Physics.LeptonTrialitySpectrum.actualSpectrum_eq,
    ``Physics.LeptonTrialitySpectrum.actual_chiral_index,
    ``Physics.LeptonTrialitySpectrum.radical_dual_trace,
    ``Physics.LeptonTrialitySpectrum.actual_forbids_all_supported,
    ``Physics.LeptonTrialitySpectrum.actual_supported,
    ``Physics.LeptonTrialitySpectrum.actual_not_weylInvariant,
    ``Physics.LeptonTrialitySpectrum.exists_joint_zeroMode,
    ``Physics.LeptonTrialitySpectrum.actual_source_counterexample]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Triality spectrum: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Triality spectrum: import boundary and {declarations.length} strict transitive axiom checks passed"
