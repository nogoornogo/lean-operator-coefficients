import Math.LieGroups.E6.Minuscule.MatrixLieAlgebra
import Lean.Util.CollectAxioms

/-!
# E6-0c: dimensions and inclusion of the actual generated matrix Lie algebras

This audit certifies finite linear/Lie data, not a compact group or a
comparison isomorphism with the pinned Geck construction.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule Minuscule.LieData SparseMatrixCertificate MatrixLieCertificate

attribute [local instance 100] LieRing.ofAssociativeRing

example : Module.finrank ℂ (matrixLieAlgebra ℂ).toSubmodule = 78 := matrixLieAlgebra_finrank ℂ
example : Module.finrank ℚ (matrixLieAlgebra ℚ).toSubmodule = 78 := matrixLieAlgebra_finrank ℚ
example : Module.finrank ℂ (d5MatrixLieAlgebra ℂ).toSubmodule = 45 := d5MatrixLieAlgebra_finrank ℂ
example : Module.finrank ℚ (d5MatrixLieAlgebra ℚ).toSubmodule = 45 := d5MatrixLieAlgebra_finrank ℚ
example : d5MatrixLieAlgebra ℂ →ₗ⁅ℂ⁆ matrixLieAlgebra ℂ := d5MatrixInclusion ℂ
example : Function.Injective (d5MatrixInclusion ℂ) := d5MatrixInclusion_injective ℂ

-- Reordered/duplicate entries are certificate syntax, not a new matrix model.
example : checkEq ([((0, 0), 2), ((0, 0), -1)] : Code (Fin 1)) [((0, 0), 1)] = true := by
  decide +kernel
example : checkEq ([((0, 0), 1)] : Code (Fin 1)) [] = false := by decide +kernel

-- Circular provenance is rejected, even if the matrices happen to vanish.
example : checkOrigin (fun _ : Fin 1 => ([] : Code (Fin 1)))
    (fun _ : Fin 1 => []) (fun _ => Sum.inr (0, 0)) 0 = false := by decide +kernel

-- Reversing the sl2 bracket or dropping the dual-pairing scale is not accepted.
example : checkEq (bracket (e6Generators 6) (e6Generators 0)) (e6Basis 12) = false := by
  decide +kernel
example : pairing (e6Dual 0) (e6Basis 0) ≠ 0 := by decide +kernel

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.SparseMatrixCertificate.eval_insert,
    ``Math.SparseMatrixCertificate.eval_normalize,
    ``Math.SparseMatrixCertificate.checkZero_sound,
    ``Math.SparseMatrixCertificate.checkEq_sound,
    ``Math.SparseMatrixCertificate.eval_mul,
    ``Math.SparseMatrixCertificate.eval_bracket,
    ``Math.SparseMatrixCertificate.eval_combination,
    ``Math.SparseMatrixCertificate.functional_realize,
    ``Math.SparseMatrixCertificate.linearIndependent_of_pairing,
    ``Math.GeneratedLieSpan.lieSpan_le_of_stable,
    ``Math.GeneratedLieSpan.span_eq_lieSpan,
    ``Math.GeneratedLieSpan.mem_of_provenance,
    ``Math.MatrixLieCertificate.generated_mem,
    ``Math.MatrixLieCertificate.span_eq_generated,
    ``Math.MatrixLieCertificate.finrank_generated,
    ``Math.E6.Minuscule.LieChecks.e6_actual_generators,
    ``Math.E6.Minuscule.LieChecks.d5_actual_generators,
    ``Math.E6.Minuscule.LieChecks.e6_generators_checked,
    ``Math.E6.Minuscule.LieChecks.d5_generators_checked,
    ``Math.E6.Minuscule.LieChecks.e6_provenance_checked,
    ``Math.E6.Minuscule.LieChecks.d5_provenance_checked,
    ``Math.E6.Minuscule.LieChecks.e6_closure_checked,
    ``Math.E6.Minuscule.LieChecks.d5_closure_checked,
    ``Math.E6.Minuscule.LieChecks.e6_scale_nonzero,
    ``Math.E6.Minuscule.LieChecks.d5_scale_nonzero,
    ``Math.E6.Minuscule.LieChecks.e6_pairing_checked,
    ``Math.E6.Minuscule.LieChecks.d5_pairing_checked,
    ``Math.E6.Minuscule.matrixLieAlgebra_span,
    ``Math.E6.Minuscule.d5MatrixLieAlgebra_span,
    ``Math.E6.Minuscule.matrixBasis_linearIndependent,
    ``Math.E6.Minuscule.d5MatrixBasis_linearIndependent,
    ``Math.E6.Minuscule.matrixLieAlgebra_finrank,
    ``Math.E6.Minuscule.d5MatrixLieAlgebra_finrank,
    ``Math.E6.Minuscule.d5_generator_eq_e6,
    ``Math.E6.Minuscule.d5MatrixLieAlgebra_le,
    ``Math.E6.Minuscule.d5MatrixInclusion,
    ``Math.E6.Minuscule.d5MatrixInclusion_injective]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0c: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0c: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0c: checked {declarations.length} declarations against the standard axiom allowlist"
