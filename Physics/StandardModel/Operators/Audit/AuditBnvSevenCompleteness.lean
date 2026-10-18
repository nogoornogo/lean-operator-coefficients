import Physics.StandardModel.Operators.BnvSevenControls
import Physics.StandardModel.Operators.BnvSevenModelInterface
import Physics.StandardModel.Operators.Audit.AuditBnvBoundedSupport

/-! Strict transitive audit of the whole dimension-seven endpoint. -/
open Lean in
run_cmd do
  let ds := [
    ``GUT.BnvSignedFieldTransport.full,
    ``GUT.BnvSignedFieldTransport.exterior,
    ``GUT.BnvSignedFieldTransport.extract_pure,
    ``GUT.BnvSignedFieldTransport.reconstruct_pure,
    ``GUT.BnvSignedFieldTransport.sectorEquiv,
    ``GUT.BnvSignedFieldTransport.negativeEquiv,
    ``GUT.BnvSixResidualCompleteness.signed_eq_partition,
    ``GUT.BnvSixResidualCompleteness.equiv,
    ``GUT.BnvSixResidualCompleteness.forbidden_iff,
    ``GUT.BnvSevenCompleteness.equiv,
    ``GUT.BnvSevenCompleteness.reconstruct_extract,
    ``GUT.BnvSevenCompleteness.extract_reconstruct,
    ``GUT.BnvSevenCompleteness.forbidden_iff,
    ``GUT.BnvSevenCompleteness.nonzero_iff,
    ``GUT.BnvSevenControls.degree_forbidden,
    ``GUT.BnvSevenControls.quarkParity_forbidden,
    ``GUT.BnvSevenControls.unitResidual_ne_zero,
    ``GUT.BnvSevenControls.positiveControl_ne_zero,
    ``GUT.BnvSevenModelInterface.piEquiv,
    ``GUT.BnvSevenModelInterface.pi_single,
    ``GUT.BnvSevenModelInterface.pull_mem,
    ``GUT.BnvSevenModelInterface.pull_symm,
    ``GUT.BnvSevenModelInterface.sectorEquiv,
    ``GUT.BnvSevenModelInterface.boundedEquiv,
    ``GUT.BnvSevenModelInterface.residualEquiv,
    ``GUT.BnvSevenModelInterface.forbidden_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "BNV seven completeness {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"BNV seven completeness: {ds.length} strict transitive checks passed"
