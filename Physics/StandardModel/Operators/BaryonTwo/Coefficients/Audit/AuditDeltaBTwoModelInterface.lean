import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoModelInterface
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``Physics.DeltaBTwoModelInterface.exists_ordered,
    ``Physics.DeltaBTwoModelInterface.onFieldsEquiv,
    ``Physics.DeltaBTwoModelInterface.exists_on_fields_iff,
    ``Physics.DeltaBTwoModelInterface.species_baryon_grade]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B model interface audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B model interface audit: {declarations.length} strict checks passed"
