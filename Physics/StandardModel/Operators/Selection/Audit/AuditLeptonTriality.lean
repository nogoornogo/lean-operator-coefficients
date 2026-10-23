import Physics.StandardModel.Operators.Selection.LeptonTriality
import Lean.Util.CollectAxioms

/-! Persistent checks for the spectrum-level counterexample. No mass-source
or quantum anomaly conclusion is asserted by this audit. -/

set_option autoImplicit false

namespace Physics.LeptonTriality.Audit

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

end Physics.LeptonTriality.Audit

run_cmd do
  let declarations := [
    ``Physics.LeptonTriality.cyclic_charge_counterexample,
    ``Physics.LeptonTriality.charges_not_orbitCompatible,
    ``Physics.LeptonTriality.character_injective,
    ``Physics.LeptonTriality.character_ne_one,
    ``Physics.LeptonTriality.label_ne_zero,
    ``Physics.LeptonTriality.label_three_nsmul,
    ``Physics.LeptonTriality.assignment_characters,
    ``Physics.LeptonTriality.family,
    ``Physics.LeptonTriality.supported_iff,
    ``Physics.LeptonTriality.supported_spectrum_counterexample,
    ``Physics.LeptonTriality.not_universal_family_obstruction,
    ``Physics.LeptonTriality.canonical_tensors_not_invariant]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Lepton triality: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Lepton triality: {declarations.length} strict transitive axiom checks passed"
