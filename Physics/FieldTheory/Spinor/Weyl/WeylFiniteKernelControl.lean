import Physics.FieldTheory.Spinor.Weyl.WeylGeneratorTests

/-! A fully discharged actual-group finite-kernel control for one left Weyl
spinor. This does not certify the general statistical SM source. -/
namespace Physics.WeylFiniteKernelControl
set_option autoImplicit false
noncomputable section
open Math Representation

def tests (i : Fin 2) : WeylSpinor.Group :=
  if i=0 then Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : ℂ)
  else Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : ℂ)

theorem upper : WeylSpinor.left (tests 0) (Pi.single 1 1) = Pi.single 1 1 + Pi.single 0 1 := by
  ext i
  fin_cases i <;> norm_num [WeylSpinor.left, tests, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two, Matrix.single]

theorem lower : WeylSpinor.left (tests 1) (Pi.single 0 1) = Pi.single 0 1 + Pi.single 1 1 := by
  ext i
  fin_cases i <;> norm_num [WeylSpinor.left, tests, Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two, Matrix.single]

theorem tests_force_zero (f : Module.Dual ℂ WeylSpinor.Space)
    (hf : ∀ i x, f (WeylSpinor.left (tests i) x) = f x) : f=0 := by
  have hu := hf 0 (Pi.single 1 1)
  rw [upper,map_add] at hu
  have hl := hf 1 (Pi.single 0 1)
  rw [lower,map_add] at hl
  have h0 : f (Pi.single 0 1)=0 := by linear_combination hu
  have h1 : f (Pi.single 1 1)=0 := by linear_combination hl
  apply (Pi.basisFun ℂ (Fin 2)).ext
  intro i
  fin_cases i
  · simpa using h0
  · simpa using h1

theorem exhaustive : FiniteInvariantKernel.Exhaustive WeylSpinor.left tests := by
  intro f hf
  rw [tests_force_zero f hf]
  intro g x
  rfl

def coefficientEquiv : InvariantCoefficientTransport.Invariants WeylSpinor.left ≃ₗ[ℂ]
    FiniteInvariantKernel.Kernel WeylSpinor.left (Pi.basisFun ℂ (Fin 2)) tests :=
  FiniteInvariantKernel.equiv _ _ _ exhaustive

theorem kernel_zero (c : FiniteInvariantKernel.Kernel WeylSpinor.left (Pi.basisFun ℂ (Fin 2)) tests) : c=0 := by
  have he := tests_force_zero ((FiniteInvariantKernel.coordinates (Pi.basisFun ℂ (Fin 2))).symm c.val)
    ((FiniteInvariantKernel.mem_kernel_iff WeylSpinor.left (Pi.basisFun ℂ (Fin 2)) tests _).mp
      (by simpa only [LinearEquiv.apply_symm_apply] using c.property))
  apply Subtype.ext
  exact ((FiniteInvariantKernel.coordinates (Pi.basisFun ℂ (Fin 2))).symm.map_eq_zero_iff).mp he

end
end Physics.WeylFiniteKernelControl
