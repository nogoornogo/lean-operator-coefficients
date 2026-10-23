import Math.RepresentationTheory.Coefficients.SpeciesCoefficientTransport
import Lean.Util.CollectAxioms

/-! Strict transitive audit of the retained completeness transport helpers. -/
run_cmd do
  let declarations := [
    ``Math.ConstrainedCompleteness.Presentation.equiv,
    ``Math.ConstrainedCompleteness.Presentation.onInputs,
    ``Math.ConstrainedCompleteness.ofEquations,
    ``Math.ConstrainedCompleteness.exists_nonzero_iff,
    ``Math.SpeciesCoefficientTransport.fieldsEquiv,
    ``Math.SpeciesCoefficientTransport.fieldsEquiv_single,
    ``Math.SpeciesCoefficientTransport.pull_mem,
    ``Math.SpeciesCoefficientTransport.pull_symm,
    ``Math.SpeciesCoefficientTransport.equiv,
    ``Math.SpeciesCoefficientTransport.complete]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Completeness transport: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Completeness transport: {declarations.length} strict transitive axiom checks passed"
