import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenControls
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenModelInterface
import Physics.StandardModel.Operators.BaryonOne.Inputs.Audit.AuditBnvBoundedSupport

/-! Strict transitive audit of the whole dimension-seven endpoint. -/
open Lean in
run_cmd do
  let ds := [
    ``Physics.BnvSignedFieldTransport.full,
    ``Physics.BnvSignedFieldTransport.exterior,
    ``Physics.BnvSignedFieldTransport.extract_pure,
    ``Physics.BnvSignedFieldTransport.reconstruct_pure,
    ``Physics.BnvSignedFieldTransport.sectorEquiv,
    ``Physics.BnvSignedFieldTransport.negativeEquiv,
    ``Physics.BnvSixResidualCompleteness.signed_eq_partition,
    ``Physics.BnvSixResidualCompleteness.equiv,
    ``Physics.BnvSixResidualCompleteness.forbidden_iff,
    ``Physics.BnvSevenCompleteness.equiv,
    ``Physics.BnvSevenCompleteness.reconstruct_extract,
    ``Physics.BnvSevenCompleteness.extract_reconstruct,
    ``Physics.BnvSevenCompleteness.forbidden_iff,
    ``Physics.BnvSevenCompleteness.nonzero_iff,
    ``Physics.BnvSevenControls.degree_forbidden,
    ``Physics.BnvSevenControls.quarkParity_forbidden,
    ``Physics.BnvSevenControls.unitResidual_ne_zero,
    ``Physics.BnvSevenControls.positiveControl_ne_zero,
    ``Physics.BnvSevenModelInterface.piEquiv,
    ``Physics.BnvSevenModelInterface.pi_single,
    ``Physics.BnvSevenModelInterface.pull_mem,
    ``Physics.BnvSevenModelInterface.pull_symm,
    ``Physics.BnvSevenModelInterface.sectorEquiv,
    ``Physics.BnvSevenModelInterface.boundedEquiv,
    ``Physics.BnvSevenModelInterface.residualEquiv,
    ``Physics.BnvSevenModelInterface.forbidden_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "BNV seven completeness {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"BNV seven completeness: {ds.length} strict transitive checks passed"
