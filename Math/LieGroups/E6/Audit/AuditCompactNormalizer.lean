import Math.LieGroups.E6.Minuscule.CompactNormalizer
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lean.Util.CollectAxioms

/-!
# E6-0g: closed compact matrix normalizer and all-time exponential criterion

No group-realization, tangent, connectedness or inclusion certificate is
assumed. A periodic scalar supplies a negative control at time one.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule NormedSpace
open scoped Matrix Matrix.Norms.L2Operator

example : CompactSpace compactNormalizer := inferInstance
example : IsTopologicalGroup compactNormalizer := inferInstance
example : Module.finrank ℝ compactMatrixLieAlgebra = 78 := compactMatrixLieAlgebra_finrank

example : IsClosed (compactNormalizer : Set (Matrix.specialUnitaryGroup (Fin 27) ℂ)) :=
  compactNormalizer_isClosed

example (X : Matrix27) : X ∈ compactMatrixLieAlgebra ↔
    ∀ t : ℝ, exp (t • X) ∈ compactNormalizerMatrices :=
  mem_compactMatrix_iff_exp_mem_normalizer X

example (k : Fin 3) (i : Fin 6) (t : ℝ) :
    exp (t • (compactGeneratorElement k i).val.val) ∈ compactNormalizerMatrices :=
  exp_generator_mem_normalizer k i t

/-- A single time, even time one, cannot replace the all-time hypothesis. -/
theorem single_exponential_not_sufficient :
    ∃ X : Matrix27, exp X ∈ compactNormalizerMatrices ∧ X ∉ compactMatrixLieAlgebra := by
  let c : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  let X : Matrix27 := c • 1
  have he : exp X = 1 := by
    have h := algebraMap_exp_comm (𝕂 := ℂ) (𝔸 := Matrix27) c
    simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.exp_eq_exp_ℂ,
      c, Complex.exp_two_pi_mul_I, one_smul] using h.symm
  refine ⟨X, ?_, ?_⟩
  · rw [he]
    exact compactNormalizerMatrices.one_mem
  · intro hX
    have ht := matrixLieAlgebra_trace X ((mem_compactMatrixLieAlgebra X).mp hX).1
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero
    have htrace : Matrix.trace X ≠ 0 := by
      simpa [X, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] using
        mul_ne_zero hc (show (27 : ℂ) ≠ 0 by norm_num)
    exact htrace ht

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.LieNormalizerExponential.exp_apply_mem,
    ``Math.LieNormalizerExponential.hasDerivAt_conjugation_zero,
    ``Math.LieNormalizerExponential.derivative_mem,
    ``Math.LieNormalizerExponential.exp_conjugate_mem,
    ``Math.LieNormalizerExponential.normalizes_iff_exp_conjugate_mem,
    ``Math.SpecialUnitaryExponentialCriterion.skew_of_exp_mem,
    ``Math.SpecialUnitaryExponentialCriterion.trace_zero_of_exp_mem,
    ``Math.SpecialUnitaryExponentialCriterion.exp_mem_iff,
    ``Math.MatrixLieGroupNormalizer.subgroup,
    ``Math.MatrixLieGroupNormalizer.conjugate_mul,
    ``Math.MatrixLieGroupNormalizer.continuous_conjugate,
    ``Math.MatrixLieGroupNormalizer.isClosed_subgroup,
    ``Math.MatrixLieGroupNormalizer.matrixCarrier_le_special,
    ``Math.MatrixLieGroupNormalizer.inverse_coe_exp,
    ``Math.MatrixLieGroupNormalizer.exp_mem_matrixCarrier_iff,
    ``Math.E6.Minuscule.compactNormalizer_isClosed,
    ``Math.E6.Minuscule.compactNormalizer_isCompact,
    ``Math.E6.Minuscule.mem_compactMatrix_iff_exp_mem_normalizer,
    ``Math.E6.Minuscule.exp_compactMatrix_mem_normalizer,
    ``Math.E6.Minuscule.exp_compactRealForm_mem_normalizer,
    ``Math.E6.Minuscule.exp_generator_mem_normalizer,
    ``Math.E6.Audit.single_exponential_not_sufficient]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0g: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0g: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0g: checked {declarations.length} declarations against the standard axiom allowlist"
