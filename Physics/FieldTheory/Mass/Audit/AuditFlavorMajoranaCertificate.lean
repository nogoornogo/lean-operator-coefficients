import Physics.FieldTheory.Mass.FlavorMajoranaCertificate
import Lean.Util.CollectAxioms

/-! Strict transitive audit of the actual physical form and certificate consumer. -/
run_cmd do
  let declarations := [
    ``GUT.FlavorMajoranaCertificate.fromDiagonal,
    ``GUT.FlavorMajoranaCertificate.ofSymmetric,
    ``GUT.FlavorMajoranaCertificate.ofSymmetric_matrix,
    ``GUT.FlavorMajoranaCertificate.fromDiagonal_surjective,
    ``GUT.FlavorMajoranaCertificate.form_symmetric,
    ``GUT.FlavorMajoranaCertificate.subgroup,
    ``GUT.FlavorMajoranaCertificate.subgroup_eq,
    ``GUT.FlavorMajoranaCertificate.classification,
    ``GUT.FlavorMajoranaCertificate.basisFreedom,
    ``GUT.FlavorMajoranaCertificate.residualHomEquiv,
    ``GUT.FlavorMajoranaCertificate.residual_nonzero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Majorana certificate interface: {declarations.length} strict transitive checks passed"
