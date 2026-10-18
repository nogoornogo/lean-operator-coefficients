import Physics.StandardModel.Operators.LeptonTriality
import Lean.Util.CollectAxioms

/-! Persistent checks for the spectrum-level counterexample. No mass-source
or quantum anomaly conclusion is asserted by this audit. -/

set_option autoImplicit false

namespace GUT.LeptonTriality.Audit

example : Fintype.card Residual = 3 := by decide

example : StandardModelLocalOperator.IsPhysicalDeltaBOneOperator
    StandardModelLocalOperator.qqueOperator :=
  StandardModelLocalOperator.qque_isPhysicalDeltaBOneOperator

example : StandardModelLocalOperator.IsPhysicalDeltaBOneOperator
    StandardModelLocalOperator.duqlOperator :=
  StandardModelLocalOperator.duql_isPhysicalDeltaBOneOperator

example : StandardAbelianCharge.ChargesSupported spectrum assignment ∧
    StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator spectrum :=
  ⟨assignment_supported, forbids_all_supported⟩

end GUT.LeptonTriality.Audit

run_cmd do
  let declarations := [
    ``GUT.LeptonTriality.cyclic_charge_counterexample,
    ``GUT.LeptonTriality.charges_not_orbitCompatible,
    ``GUT.LeptonTriality.character_injective,
    ``GUT.LeptonTriality.character_ne_one,
    ``GUT.LeptonTriality.label_ne_zero,
    ``GUT.LeptonTriality.label_three_nsmul,
    ``GUT.LeptonTriality.assignment_characters,
    ``GUT.LeptonTriality.family,
    ``GUT.LeptonTriality.supported_iff,
    ``GUT.LeptonTriality.supported_spectrum_counterexample,
    ``GUT.LeptonTriality.not_universal_family_obstruction,
    ``GUT.LeptonTriality.canonical_tensors_not_invariant]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Lepton triality: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Lepton triality: {declarations.length} strict transitive axiom checks passed"
