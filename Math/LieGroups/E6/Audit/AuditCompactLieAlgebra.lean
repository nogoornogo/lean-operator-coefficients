import Math.LieGroups.E6.Minuscule.CompactLieAlgebra
import Math.LieGroups.E6.Audit.AuditCompactTangent

/-! # E6-0n: actual geometric tangent Lie bracket, not a substituted model bracket -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

attribute [local instance] LieGroup.minSmoothnessThree

example : Nonempty
    (GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent ≃ₗ⁅ℝ⁆
      compactRealForm) := ⟨compactTangentRealFormLieEquiv⟩

example : Function.Injective compactUnits := compactUnits_injective

example (g : compactIdentityComponent) : (compactUnits g : Matrix27) = compactMatrix g := rfl

example (X Y : GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent) :
    (compactTangentEquiv (VectorField.mlieBracket 𝓘(ℝ, compactMatrixLieAlgebra)
      (mulInvariantVectorField X) (mulInvariantVectorField Y) 1) : Matrix27) =
      (compactTangentEquiv X : Matrix27) * (compactTangentEquiv Y : Matrix27) -
        (compactTangentEquiv Y : Matrix27) * (compactTangentEquiv X : Matrix27) :=
  compact_invariantVectorField_bracket X Y

example (X : GroupLieAlgebra 𝓘(ℝ, compactMatrixLieAlgebra) compactIdentityComponent) :
    compactTangentLieEquiv X = compactTangentEquiv X := rfl

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.compactUnits,
    ``Math.E6.Minuscule.compactUnits_val,
    ``Math.E6.Minuscule.compactUnits_injective,
    ``Math.E6.Minuscule.compactUnits_writtenInExtChartAt_one,
    ``Math.E6.Minuscule.compactUnits_mfderiv_one,
    ``Math.E6.Minuscule.compactTangentMatrixLieHom,
    ``Math.E6.Minuscule.compactTangentMatrixLieHom_apply,
    ``Math.E6.Minuscule.compactTangentLieEquiv,
    ``Math.E6.Minuscule.compactTangentLieEquiv_apply,
    ``Math.E6.Minuscule.compact_invariantVectorField_bracket,
    ``Math.E6.Minuscule.compactTangentRealFormLieEquiv]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0n: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0n: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0n: checked {declarations.length} declarations against the standard axiom allowlist"
