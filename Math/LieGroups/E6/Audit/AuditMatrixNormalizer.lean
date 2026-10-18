import Math.LieGroups.E6.Minuscule.MatrixNormalizer
import Lean.Util.CollectAxioms

/-!
# E6-0f: actual scalar commutant and trace-zero normalizer

The concrete statements assume no irreducibility, commutant or innerness
certificate. Negative controls retain the essential trace restriction.
This audit does not identify any Lie group or integrate a homomorphism.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule
open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

example (M : Matrix27) (hE : ∀ i, Commute M (raising i))
    (hF : ∀ i, Commute M (lowering i)) : M = M 0 0 • (1 : Matrix27) :=
  commutant_scalar_of_generators M hE hF

example : LieAlgebra.IsKilling ℂ (matrixLieAlgebra ℂ) := inferInstance
example : Module.finrank ℝ compactMatrixLieAlgebra = 78 := compactMatrixLieAlgebra_finrank
example : compactRealForm ≃ₗ⁅ℝ⁆ compactMatrixLieAlgebra := compactMatrixEquiv

example (A : Matrix27) :
    A ∈ matrixLieAlgebra ℂ ↔ A ∈ (matrixLieAlgebra ℂ).normalizer ∧ Matrix.trace A = 0 :=
  matrixLieAlgebra_mem_iff_normalizes_trace_zero A

example (A : Matrix27) :
    A ∈ compactMatrixLieAlgebra ↔
      A ∈ compactMatrixLieAlgebra.normalizer ∧ Aᴴ = -A ∧ Matrix.trace A = 0 :=
  compactMatrix_mem_iff_normalizes_skew_trace_zero A

theorem identity_normalizes_not_mem :
    (1 : Matrix27) ∈ (matrixLieAlgebra ℂ).normalizer ∧ (1 : Matrix27) ∉ matrixLieAlgebra ℂ := by
  constructor
  · rw [LieSubalgebra.mem_normalizer_iff]
    intro x _
    simp [Ring.lie_def]
  · intro h
    have ht := matrixLieAlgebra_trace _ h
    norm_num [Matrix.trace_one] at ht

-- Even a skew-Hermitian normalizer need not have trace zero.
theorem imaginary_identity_normalizes_not_mem :
    Complex.I • (1 : Matrix27) ∈ compactMatrixLieAlgebra.normalizer ∧
      (Complex.I • (1 : Matrix27))ᴴ = -(Complex.I • (1 : Matrix27)) ∧
      Complex.I • (1 : Matrix27) ∉ compactMatrixLieAlgebra := by
  refine ⟨?_, ?_, ?_⟩
  · rw [LieSubalgebra.mem_normalizer_iff]
    intro x _
    simp [Ring.lie_def]
  · simp [Matrix.conjTranspose_smul]
  · intro h
    have ht := matrixLieAlgebra_trace _ ((mem_compactMatrixLieAlgebra _).mp h).1
    norm_num [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul] at ht

-- Cartan commutation alone is not the scalar-commutant theorem.
theorem cartan_zero_not_scalar : ¬∃ c : ℂ, cartan 0 = c • (1 : Matrix27) := by
  rintro ⟨c, hc⟩
  have h0 := congrArg (fun X : Matrix27 => X 0 0) hc
  have h1 := congrArg (fun X : Matrix27 => X 1 1) hc
  norm_num [cartan_eq_diagonal, TauCeti.DynkinType.e6MinusculeWeight] at h0 h1
  have := h0.trans h1.symm
  norm_num at this

example (i : Fin 6) : Commute (cartan 0) (cartan i) := by
  simp only [cartan_eq_diagonal]
  exact Matrix.commute_diagonal _ _

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.MatrixLieNormalizer.derivation,
    ``Math.MatrixLieNormalizer.normalizer_decomposition,
    ``Math.MatrixLieNormalizer.mem_of_normalizes_of_trace_zero,
    ``Math.MatrixLieNormalizer.mem_iff_normalizes_and_trace_zero,
    ``Math.E6.Minuscule.cartan_eq_diagonal,
    ``Math.E6.Minuscule.cartan_eq_lie,
    ``Math.E6.Minuscule.raising_predecessor,
    ``Math.E6.Minuscule.offDiagonal_eq_zero_of_commute_cartan,
    ``Math.E6.Minuscule.eq_diagonal_of_commute_cartan,
    ``Math.E6.Minuscule.diagonal_eq_of_raising_edge,
    ``Math.E6.Minuscule.diagonal_constant,
    ``Math.E6.Minuscule.commutant_scalar_of_cartan_raising,
    ``Math.E6.Minuscule.commutant_scalar_of_generators,
    ``Math.E6.Minuscule.matrixLieAlgebra_commutant_scalar,
    ``Math.E6.Minuscule.matrixLieAlgebra_commutant_iff,
    ``Math.E6.Minuscule.matrixLieAlgebra_isKilling,
    ``Math.E6.Minuscule.matrixNormalizer_decomposition,
    ``Math.E6.Minuscule.matrixLieAlgebra_mem_iff_normalizes_trace_zero,
    ``Math.E6.Minuscule.compactMatrixEquiv,
    ``Math.E6.Minuscule.compactMatrixLieAlgebra_finrank,
    ``Math.E6.Minuscule.mem_compactMatrixLieAlgebra,
    ``Math.E6.Minuscule.normalizes_complex_of_normalizes_real,
    ``Math.E6.Minuscule.compactMatrix_mem_iff_normalizes_skew_trace_zero,
    ``Math.E6.Audit.identity_normalizes_not_mem,
    ``Math.E6.Audit.imaginary_identity_normalizes_not_mem,
    ``Math.E6.Audit.cartan_zero_not_scalar]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0f: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0f: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0f: checked {declarations.length} declarations against the standard axiom allowlist"
