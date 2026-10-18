import Math.LinearAlgebra.TakagiExistence
import Lean.Util.CollectAxioms

/-! Strict transitive audit: no Takagi or eigenbasis premise is imported as an axiom. -/
run_cmd do
  let declarations := [
    ``Math.AntilinearSpectral.realMap,
    ``Math.AntilinearSpectral.exists_unit_eigenvector,
    ``Math.AntilinearSpectral.exists_basis,
    ``Math.TakagiExistence.anti_add,
    ``Math.TakagiExistence.anti_smul,
    ``Math.TakagiExistence.inner_anti,
    ``Math.TakagiExistence.anti_symmetric,
    ``Math.TakagiExistence.exists_real_diagonal,
    ``Math.TakagiExistence.exists_nonnegative_diagonal,
    ``Math.TakagiExistence.symmetric_iff_exists_nonnegative_diagonal,
    ``Math.TakagiExistence.singular_nondiagonal_control,
    ``Math.TakagiExistence.nonsymmetric_control]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Takagi existence: {declarations.length} strict transitive checks passed"
