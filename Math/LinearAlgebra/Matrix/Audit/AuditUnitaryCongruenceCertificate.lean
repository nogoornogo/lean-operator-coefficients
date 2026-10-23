import Math.LinearAlgebra.Matrix.UnitaryCongruenceCertificate
import Lean.Util.CollectAxioms

/-! Strict transitive audit of certificate transport and exact basis freedom. -/
run_cmd do
  let declarations := [
    ``Math.UnitaryCongruenceCertificate.comp,
    ``Math.UnitaryCongruenceCertificate.inverse,
    ``Math.UnitaryCongruenceCertificate.subgroup,
    ``Math.UnitaryCongruenceCertificate.bilinear_iff,
    ``Math.UnitaryCongruenceCertificate.congruenceEquiv,
    ``Math.UnitaryCongruenceCertificate.diagonal_subgroup,
    ``Math.UnitaryCongruenceCertificate.classification,
    ``Math.UnitaryCongruenceCertificate.certificateEquiv,
    ``Math.UnitaryCongruenceCertificate.exists_unique_difference,
    ``Math.UnitaryCongruenceCertificate.residualHomEquiv,
    ``Math.UnitaryCongruenceCertificate.residual_nonzero_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Unitary congruence certificate: {declarations.length} strict transitive checks passed"
