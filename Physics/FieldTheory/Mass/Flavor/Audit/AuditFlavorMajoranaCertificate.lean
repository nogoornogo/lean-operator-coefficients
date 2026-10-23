import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaCertificate
import Lean.Util.CollectAxioms

/-! Strict transitive audit of the actual physical form and certificate consumer. -/
run_cmd do
  let declarations := [
    ``Physics.FlavorMajoranaCertificate.fromDiagonal,
    ``Physics.FlavorMajoranaCertificate.ofSymmetric,
    ``Physics.FlavorMajoranaCertificate.ofSymmetric_matrix,
    ``Physics.FlavorMajoranaCertificate.fromDiagonal_surjective,
    ``Physics.FlavorMajoranaCertificate.form_symmetric,
    ``Physics.FlavorMajoranaCertificate.subgroup,
    ``Physics.FlavorMajoranaCertificate.subgroup_eq,
    ``Physics.FlavorMajoranaCertificate.classification,
    ``Physics.FlavorMajoranaCertificate.basisFreedom,
    ``Physics.FlavorMajoranaCertificate.residualHomEquiv,
    ``Physics.FlavorMajoranaCertificate.residual_nonzero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Majorana certificate interface: {declarations.length} strict transitive checks passed"
