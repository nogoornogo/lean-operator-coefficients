import Math.RepresentationTheory.Jets.DerivativeProhibition
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarDerivativeInterface

/-! A concrete necessary parameter condition from the full Lorentz EOM/IBP
input. No graded on-shell decomposition or coefficient extension is assumed. -/
namespace Physics.ScalarProhibitionConditions
set_option autoImplicit false
noncomputable section
open Math PolynomialScalarEOM DerivativeProhibition

theorem wave_is_divergence : LorentzJetIBP.waveField =
    D 0 (D 0 field)-D 1 (D 1 field)-D 2 (D 2 field)-D 3 (D 3 field) := by
  simp [MasslessScalarEOM.waveField_formula,field,MasslessScalarEOM.field,
    ScalarJetAlgebra.totalDerivative_X,ScalarJetAlgebra.shift,← Finsupp.single_add]

theorem wave_mem (lambda : ℂ) : LorentzJetIBP.waveField ∈
    (ScalarDerivativeInterface.scalar lambda).relations := by
  rw [wave_is_divergence]
  exact Submodule.mem_sup_right
    ((DifferentialEquation.ibp D).sub_mem
      ((DifferentialEquation.ibp D).sub_mem
        ((DifferentialEquation.ibp D).sub_mem
          (DifferentialEquation.derivative_mem_ibp D 0 _)
          (DifferentialEquation.derivative_mem_ibp D 1 _))
        (DifferentialEquation.derivative_mem_ibp D 2 _))
      (DifferentialEquation.derivative_mem_ibp D 3 _))

theorem wave_coefficient_zero (lambda : ℂ)
    (f : (ScalarDerivativeInterface.scalar lambda).Coefficient) :
    f.val LorentzJetIBP.waveField = 0 := f.property (wave_mem lambda)

theorem cubic_constraint (lambda : ℂ)
    (f : (ScalarDerivativeInterface.scalar lambda).Coefficient) :
    lambda*f.val (field^3) = 0 := by
  have h := ScalarInputAdapter.lorentz_interaction_constraint lambda f
  change f.val LorentzJetIBP.waveField + lambda*f.val (field^3) = 0 at h
  rw [wave_coefficient_zero lambda f,zero_add] at h
  exact h

theorem nonzero_cubic_requires_zero_coupling (lambda : ℂ)
    (h : ∃ f : (ScalarDerivativeInterface.scalar lambda).Coefficient, f.val (field^3) ≠ 0) :
    lambda = 0 := by
  obtain ⟨f,hf⟩ := h
  exact (mul_eq_zero.mp (cubic_constraint lambda f)).resolve_right hf

theorem cubic_zero_of_coupling (lambda : ℂ) (hl : lambda ≠ 0)
    (f : (ScalarDerivativeInterface.scalar lambda).Coefficient) : f.val (field^3) = 0 :=
  (mul_eq_zero.mp (cubic_constraint lambda f)).resolve_left hl

theorem selected_wave_zero (lambda : ℂ)
    (f : (ScalarDerivativeInterface.selected lambda).Coefficient) :
    f.val ScalarDerivativeInterface.wave = 0 := by
  apply f.property
  exact wave_mem lambda

theorem selected_cubic_zero (lambda : ℂ) (hl : lambda ≠ 0)
    (f : (ScalarDerivativeInterface.selected lambda).Coefficient) :
    f.val ScalarDerivativeInterface.cubic = 0 := by
  have h := ScalarDerivativeInterface.selected_interaction lambda f
  rw [selected_wave_zero lambda f,zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hl

end
end Physics.ScalarProhibitionConditions
