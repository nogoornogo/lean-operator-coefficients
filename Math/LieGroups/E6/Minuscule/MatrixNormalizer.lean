import Math.LieGroups.E6.Minuscule.MatrixCommutant
import Math.LieGroups.Matrix.MatrixLieNormalizer

/-!
# Exact infinitesimal normalizer bounds for the E6 minuscule matrices

The trace-zero complex Lie normalizer is precisely the E6 matrix algebra.
This must not be confused with identifying the Lie algebra, components or
global form of a topological group normalizer.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open scoped Matrix TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

instance matrixLieAlgebra_isKilling : LieAlgebra.IsKilling ℂ (matrixLieAlgebra ℂ) :=
  (matrixGeckEquiv ℂ).symm.isKilling

theorem matrixNormalizer_decomposition (A : Matrix27) (hA : A ∈ (matrixLieAlgebra ℂ).normalizer) :
    ∃ z : matrixLieAlgebra ℂ, ∃ c : ℂ, A = (z : Matrix27) + c • 1 :=
  MatrixLieNormalizer.normalizer_decomposition _
    (fun M hM => ⟨M 0 0, matrixLieAlgebra_commutant_scalar M hM⟩) A hA

theorem matrixLieAlgebra_mem_iff_normalizes_trace_zero (A : Matrix27) :
    A ∈ matrixLieAlgebra ℂ ↔ A ∈ (matrixLieAlgebra ℂ).normalizer ∧ Matrix.trace A = 0 :=
  MatrixLieNormalizer.mem_iff_normalizes_and_trace_zero _
    (fun M hM => ⟨M 0 0, matrixLieAlgebra_commutant_scalar M hM⟩)
    matrixLieAlgebra_trace A

/-- The ambient-matrix carrier of the already constructed real form. -/
def compactMatrixLieAlgebra : LieSubalgebra ℝ Matrix27 :=
  (MatrixCompactRealForm.representation (matrixLieAlgebra ℂ) matrixLieAlgebra_adjoint).range

def compactMatrixEquiv : compactRealForm ≃ₗ⁅ℝ⁆ compactMatrixLieAlgebra :=
  (MatrixCompactRealForm.representation _ _).equivRangeOfInjective
    (MatrixCompactRealForm.representation_injective _ _)

theorem compactMatrixLieAlgebra_finrank : Module.finrank ℝ compactMatrixLieAlgebra = 78 :=
  compactMatrixEquiv.toLinearEquiv.finrank_eq.symm.trans compactRealForm_finrank

theorem mem_compactMatrixLieAlgebra (A : Matrix27) :
    A ∈ compactMatrixLieAlgebra ↔ A ∈ matrixLieAlgebra ℂ ∧ Aᴴ = -A := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val.property, (MatrixCompactRealForm.mem_realForm _ _ _).mp x.property⟩
  · rintro ⟨hA, hskew⟩
    exact ⟨⟨⟨A, hA⟩, (MatrixCompactRealForm.mem_realForm _ _ _).mpr hskew⟩, rfl⟩

/-- Normalizing the real form also normalizes its complexification. -/
theorem normalizes_complex_of_normalizes_real (A : Matrix27)
    (hA : A ∈ compactMatrixLieAlgebra.normalizer) : A ∈ (matrixLieAlgebra ℂ).normalizer := by
  rw [LieSubalgebra.mem_normalizer_iff]
  intro x hx
  let K := MatrixCompactRealForm.conjugation (matrixLieAlgebra ℂ) matrixLieAlgebra_adjoint
  have hK : Function.Involutive K := MatrixCompactRealForm.conjugation_involutive _ _
  let r : compactRealForm := ⟨TauCeti.conjRealPart K ⟨x, hx⟩, TauCeti.conjRealPart_mem hK _⟩
  let s : compactRealForm :=
    ⟨TauCeti.conjImaginaryPart K ⟨x, hx⟩, TauCeti.conjImaginaryPart_mem hK _⟩
  have hdecomp : r.val.val + Complex.I • s.val.val = x :=
    congrArg (fun z : matrixLieAlgebra ℂ => (z : Matrix27))
      (TauCeti.conjRealPart_add_I_smul_conjImaginaryPart (K := K) ⟨x, hx⟩)
  have hpart (v : compactRealForm) : ⁅A, v.val.val⁆ ∈ matrixLieAlgebra ℂ := by
    have hv : v.val.val ∈ compactMatrixLieAlgebra := ⟨v, rfl⟩
    exact ((mem_compactMatrixLieAlgebra _).mp
      ((compactMatrixLieAlgebra.mem_normalizer_iff A).mp hA _ hv)).1
  rw [← hdecomp, lie_add, lie_smul]
  exact (matrixLieAlgebra ℂ).add_mem (hpart r) ((matrixLieAlgebra ℂ).smul_mem _ (hpart s))

/-- No extra traceless skew-Hermitian infinitesimal normalizers occur. -/
theorem compactMatrix_mem_iff_normalizes_skew_trace_zero (A : Matrix27) :
    A ∈ compactMatrixLieAlgebra ↔
      A ∈ compactMatrixLieAlgebra.normalizer ∧ Aᴴ = -A ∧ Matrix.trace A = 0 := by
  constructor
  · intro hA
    obtain ⟨hL, hs⟩ := (mem_compactMatrixLieAlgebra A).mp hA
    exact ⟨compactMatrixLieAlgebra.le_normalizer hA, hs, matrixLieAlgebra_trace A hL⟩
  · rintro ⟨hn, hs, ht⟩
    exact (mem_compactMatrixLieAlgebra A).mpr
      ⟨(matrixLieAlgebra_mem_iff_normalizes_trace_zero A).mpr
        ⟨normalizes_complex_of_normalizes_real A hn, ht⟩, hs⟩

end

end Math.E6.Minuscule
