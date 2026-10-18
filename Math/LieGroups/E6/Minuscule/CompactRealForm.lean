import Math.LieGroups.E6.Minuscule.GeckComparison
import Math.LieGroups.E6.Minuscule.CompactExponentials
import Math.LieGroups.Matrix.MatrixCompactRealForm

/-!
# Actual skew-Hermitian real forms of the E6 and D5 matrix algebras

Their complexifications are the pinned Geck Lie algebras. The real D5
inclusion is injective and compatible with the complex matrix inclusion.
This is not a construction or identification of global compact groups.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open TauCeti.E6Minuscule TauCeti.DynkinType
open scoped Matrix TensorProduct Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

theorem matrixLieAlgebra_adjoint (x : Matrix27) (hx : x ∈ matrixLieAlgebra ℂ) :
    xᴴ ∈ matrixLieAlgebra ℂ := by
  rw [← generated_eq_matrixLieAlgebra] at hx ⊢
  exact MatrixCompactRealForm.adjoint_mem_lieSpan raising lowering raising_adjoint x hx

theorem d5MatrixLieAlgebra_adjoint (x : Matrix27) (hx : x ∈ d5MatrixLieAlgebra ℂ) :
    xᴴ ∈ d5MatrixLieAlgebra ℂ := by
  rw [← generated_eq_d5MatrixLieAlgebra] at hx ⊢
  exact MatrixCompactRealForm.adjoint_mem_lieSpan (raising ∘ d5Node)
    (lowering ∘ d5Node) (fun i => raising_adjoint (d5Node i)) x hx

abbrev compactRealForm :=
  MatrixCompactRealForm.realForm (matrixLieAlgebra ℂ) matrixLieAlgebra_adjoint

abbrev d5CompactRealForm :=
  MatrixCompactRealForm.realForm (d5MatrixLieAlgebra ℂ) d5MatrixLieAlgebra_adjoint

theorem compactRealForm_finrank : Module.finrank ℝ compactRealForm = 78 :=
  (MatrixCompactRealForm.finrank_realForm _ _).trans (matrixLieAlgebra_finrank ℂ)

theorem d5CompactRealForm_finrank : Module.finrank ℝ d5CompactRealForm = 45 :=
  (MatrixCompactRealForm.finrank_realForm _ _).trans (d5MatrixLieAlgebra_finrank ℂ)

/-- The real matrix algebra complexifies to the actual E6 Geck carrier. -/
def compactGeckEquiv : ℂ ⊗[ℝ] compactRealForm ≃ₗ⁅ℂ⁆ E6.lieAlgebraBaseChange valid_E6 ℂ :=
  (MatrixCompactRealForm.complexification _ _).trans (matrixGeckEquiv ℂ)

def d5CompactGeckEquiv :
    ℂ ⊗[ℝ] d5CompactRealForm ≃ₗ⁅ℂ⁆ (D 5).lieAlgebraBaseChange valid_D5 ℂ :=
  (MatrixCompactRealForm.complexification _ _).trans (d5MatrixGeckEquiv ℂ)

def compactD5Inclusion : d5CompactRealForm →ₗ⁅ℝ⁆ compactRealForm :=
  MatrixCompactRealForm.inclusion _ _ _ _ (d5MatrixLieAlgebra_le ℂ)

theorem compactD5Inclusion_injective : Function.Injective compactD5Inclusion :=
  MatrixCompactRealForm.inclusion_injective _ _ _ _ _

@[simp] theorem compactD5Inclusion_val (x : d5CompactRealForm) :
    (compactD5Inclusion x).val.val = x.val.val := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Complexifying the real inclusion gives the checked Geck D5 inclusion. -/
theorem compactGeckEquiv_inclusion (z : ℂ ⊗[ℝ] d5CompactRealForm) :
    compactGeckEquiv (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) compactD5Inclusion z) =
      geckD5Inclusion ℂ (d5CompactGeckEquiv z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c x =>
    simp only [LieAlgebra.ExtendScalars.map_apply_tmul, AlgHom.id_apply,
      compactGeckEquiv, d5CompactGeckEquiv, LieEquiv.trans_apply,
      MatrixCompactRealForm.complexification_tmul, map_smul]
    congr 1
    simp only [geckD5Inclusion, LieHom.comp_apply, LieEquiv.coe_toLieHom,
      LieEquiv.symm_apply_apply]
    rfl

theorem raising_mem_matrixLieAlgebra (i : Fin 6) : raising i ∈ matrixLieAlgebra ℂ := by
  rw [← generated_eq_matrixLieAlgebra]
  exact (SerreMatrixBasis.e ℂ raisingMatrix loweringMatrix i).property

theorem lowering_mem_matrixLieAlgebra (i : Fin 6) : lowering i ∈ matrixLieAlgebra ℂ := by
  rw [← generated_eq_matrixLieAlgebra]
  exact (SerreMatrixBasis.f ℂ raisingMatrix loweringMatrix i).property

theorem cartan_mem_matrixLieAlgebra (i : Fin 6) : cartan i ∈ matrixLieAlgebra ℂ := by
  rw [← generated_eq_matrixLieAlgebra]
  exact (SerreMatrixBasis.h ℂ _ _ _ isSerreSystem i).property

theorem compactGenerator_mem_matrixLieAlgebra (k : Fin 3) (i : Fin 6) :
    compactGenerator k i ∈ matrixLieAlgebra ℂ := by
  fin_cases k
  · exact (matrixLieAlgebra ℂ).sub_mem
      (raising_mem_matrixLieAlgebra i) (lowering_mem_matrixLieAlgebra i)
  · exact (matrixLieAlgebra ℂ).smul_mem _ ((matrixLieAlgebra ℂ).add_mem
      (raising_mem_matrixLieAlgebra i) (lowering_mem_matrixLieAlgebra i))
  · exact (matrixLieAlgebra ℂ).smul_mem _ (cartan_mem_matrixLieAlgebra i)

/-- The previously checked compact generators inhabit the actual real form. -/
def compactGeneratorElement (k : Fin 3) (i : Fin 6) : compactRealForm :=
  ⟨⟨compactGenerator k i, compactGenerator_mem_matrixLieAlgebra k i⟩,
    (MatrixCompactRealForm.mem_realForm _ _ _).mpr (compactGenerator_adjoint k i)⟩

theorem matrixLieAlgebra_trace (x : Matrix27) (hx : x ∈ matrixLieAlgebra ℂ) :
    Matrix.trace x = 0 := by
  rw [← generated_eq_matrixLieAlgebra] at hx
  change x ∈ LieSubalgebra.lieSpan ℂ Matrix27 (Set.range raising ∪ Set.range lowering) at hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact raising_trace i
    · exact lowering_trace i
  | zero => simp
  | add x y hx hy ihx ihy => simp only [Matrix.trace_add, ihx, ihy, add_zero]
  | smul c x hx ih => simp only [Matrix.trace_smul, ih, smul_zero]
  | lie x y hx hy ihx ihy =>
    rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- Every direction of this real Lie algebra exponentiates into actual SU(27). -/
theorem exp_compactRealForm_mem (x : compactRealForm) (t : ℝ) :
    NormedSpace.exp (t • x.val.val) ∈ Matrix.specialUnitaryGroup (Fin 27) ℂ := by
  let : NormedAlgebra ℚ Matrix27 := NormedAlgebra.restrictScalars ℚ ℂ Matrix27
  let : IsScalarTower ℚ ℂ Matrix27 := IsScalarTower.restrictScalars ℚ ℂ Matrix27
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    apply skewAdjoint.smul_mem
    exact (MatrixCompactRealForm.mem_realForm _ _ _).mp x.property
  · rw [MatrixDeterminantExponential.det_exp, Matrix.trace_smul,
      matrixLieAlgebra_trace _ x.val.property, smul_zero, Complex.exp_zero]

end

end Math.E6.Minuscule
