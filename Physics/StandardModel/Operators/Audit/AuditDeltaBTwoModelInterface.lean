import Physics.StandardModel.Operators.DeltaBTwoModelInterface
import Lean.Util.CollectAxioms

run_cmd do
  let declarations := [
    ``GUT.DeltaBTwoModelInterface.exists_ordered,
    ``GUT.DeltaBTwoModelInterface.onFieldsEquiv,
    ``GUT.DeltaBTwoModelInterface.exists_on_fields_iff,
    ``GUT.DeltaBTwoModelInterface.species_baryon_grade]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B model interface audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B model interface audit: {declarations.length} strict checks passed"
