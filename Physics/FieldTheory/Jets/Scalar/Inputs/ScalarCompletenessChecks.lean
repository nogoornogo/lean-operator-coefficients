import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarQuarticContractions

/-! Actual-input consumers and scope controls for the added C1/C2 results.
The Cao comparison is an algebraic reading of 2105.12742v3 (3.28)-(3.29),
not a conformal-primary, scattering or renormalization theorem. -/
namespace Physics.ScalarCompletenessChecks
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM

namespace Two
open ScalarQuarticTwoCompleteness

theorem global_zero (f : P.Coefficient) (p : V) : f.val p.val = 0 := by
  have h := selected_forbidden (P.restrict V stable f)
  have he := congrArg (fun F : selected.Coefficient => F.val p) h
  exact he

theorem helper_zero (f : (DerivativeLiteratureScalar.quarticInput 0).Coefficient) (p : V) :
    f.val p.val = 0 := global_zero (DerivativeLiteratureScalar.toDirect 0 f) p

def anisotropic : OffShell := field^2*(D 0 field)^2

theorem anisotropic_grade : anisotropic ∈ V := by
  simpa only [anisotropic,pow_two,mul_assoc,LorentzFiniteControls.E,linearFirst_single] using
    product_grade (LorentzFiniteControls.E 0) (LorentzFiniteControls.E 0)

theorem anisotropic_value : ScalarQuarticFourWitness.separator anisotropic = -8 := by
  open FourWaveEvaluation ScalarQuarticFourWitness in
  change coefficient (ev (field^2*(D 0 field)^2)) = -8
  rw [map_mul,map_pow,map_pow,field_value,first_value]
  norm_num [momenta,Fin.sum_univ_succ]
  have ht : (X 0 : FourWaveEvaluation.P)+(X 1+(-X 2+-X 3)) = X 0+X 1-X 2-X 3 := by ring
  rw [ht]
  have hp : ((X 0 : FourWaveEvaluation.P)+X 1+X 2+X 3)^2*
      (X 0+X 1-X 2-X 3)^2 =
      (X 0+X 1)^4+(X 2+X 3)^4-C (2:ℂ)*(
        X 0^2*X 2^2+X 0^2*X 3^2+X 1^2*X 2^2+X 1^2*X 3^2+
        C (2:ℂ)*X 0^2*X 2*X 3+C (2:ℂ)*X 1^2*X 2*X 3+
        C (2:ℂ)*X 0*X 1*X 2^2+C (2:ℂ)*X 0*X 1*X 3^2+
        C (4:ℂ)*X 0*X 1*X 2*X 3) := by
    norm_num only [map_ofNat]
    ring
  rw [hp,map_sub,map_add]
  have h01 : coefficient (((X 0 : FourWaveEvaluation.P)+X 1)^4) = 0 := by
    simpa [Fin.sum_univ_succ,Fin.prod_univ_succ] using
      coefficient_fourth (![1,1,0,0] : Fin 4 → ℂ)
  have h23 : coefficient (((X 2 : FourWaveEvaluation.P)+X 3)^4) = 0 := by
    simpa [Fin.sum_univ_succ,Fin.prod_univ_succ] using
      coefficient_fourth (![0,0,1,1] : Fin 4 → ℂ)
  rw [h01,h23]
  simp only [coefficient,lcoeff_apply,X_pow_eq_monomial]
  simp only [X,mul_add,C_mul_monomial,monomial_mul_monomial]
  norm_num [squareFree,Fin.sum_univ_succ,coeff_monomial,Finsupp.ext_iff,Fin.forall_fin_succ]

theorem anisotropic_nonzero : P.projection anisotropic ≠ 0 := by
  intro hz
  have h := ScalarQuarticFourWitness.annihilates ((Submodule.Quotient.mk_eq_zero _).mp hz)
  change ScalarQuarticFourWitness.separator anisotropic = 0 at h
  rw [anisotropic_value] at h
  norm_num at h

theorem anisotropic_coefficient_rejected :
    ¬∃ f : P.Coefficient, f.val anisotropic = 1 := by
  rintro ⟨f,hf⟩
  have he := global_zero f ⟨anisotropic,anisotropic_grade⟩
  rw [hf] at he
  exact one_ne_zero he

end Two

namespace Four
open ScalarQuarticContractions

theorem helper_nonzero :
    (DerivativeLiteratureScalar.quarticInput 0).projection C4 ≠ 0 := by
  intro hz
  have hp := (Submodule.Quotient.mk_eq_zero _).mp hz
  change C4 ∈ DifferentialEquation.combined D
    (DerivativeLiteratureScalar.quarticDensity 0).scalarSeeds at hp
  rw [DerivativeLiteratureScalar.quartic_relations] at hp
  exact ScalarQuarticFourWitness.quotient_nonzero ((Submodule.Quotient.mk_eq_zero _).mpr hp)

theorem coefficient_A (f : (ScalarDerivativeInterface.scalar 0).Coefficient) :
    f.val A = f.val C4 := by
  have h := congrArg ((ScalarDerivativeInterface.scalar 0).coefficientEquiv f) A_eq_C4
  exact h

theorem coefficient_B (f : (ScalarDerivativeInterface.scalar 0).Coefficient) :
    f.val B = (-1/2:ℂ)*f.val C4 := by
  have h := congrArg ((ScalarDerivativeInterface.scalar 0).coefficientEquiv f) B_eq_C4
  rw [map_smul] at h
  change f.val B = (-1/2:ℂ) • f.val C4 at h
  exact h

theorem helper_coefficients (f : (DerivativeLiteratureScalar.quarticInput 0).Coefficient) :
    f.val A = f.val C4 ∧ f.val B = (-1/2:ℂ)*f.val C4 :=
  ⟨coefficient_A (DerivativeLiteratureScalar.toDirect 0 f),
    coefficient_B (DerivativeLiteratureScalar.toDirect 0 f)⟩

end Four

namespace Cao
open ScalarQuarticContractions
def o1 : OffShell := (1/4:ℂ) • A
def o2 : OffShell := (1/2:ℂ) • B
def o3 : OffShell := (1/8:ℂ) • C4
def combination : OffShell := o1-(2:ℂ) • o2+(6:ℂ) • o3

theorem quotient_normalization : q combination = (3/2:ℂ) • q C4 := by
  simp only [combination,o1,o2,o3,map_add,map_sub,map_smul,A_eq_C4,B_eq_C4,smul_smul]
  module

theorem nonzero : q combination ≠ 0 := by
  rw [quotient_normalization]
  exact smul_ne_zero (by norm_num) ScalarQuarticFourWitness.quotient_nonzero

theorem separator_value : ScalarQuarticFourWitness.separator combination = 72 := by
  let L : (ScalarDerivativeInterface.scalar 0).Source →ₗ[ℂ] ℂ :=
    (ScalarDerivativeInterface.scalar 0).relations.liftQ
      ScalarQuarticFourWitness.separator ScalarQuarticFourWitness.annihilates
  have h := congrArg L quotient_normalization
  change ScalarQuarticFourWitness.separator combination =
    L ((3/2:ℂ) • q C4) at h
  rw [map_smul] at h
  change ScalarQuarticFourWitness.separator combination =
    (3/2:ℂ) • ScalarQuarticFourWitness.separator C4 at h
  rw [ScalarQuarticFourWitness.four_value] at h
  norm_num at h
  exact h

theorem coefficient_value (f : (ScalarDerivativeInterface.scalar 0).Coefficient) :
    f.val combination = (3/2:ℂ)*f.val C4 := by
  have h := congrArg ((ScalarDerivativeInterface.scalar 0).coefficientEquiv f) quotient_normalization
  rw [map_smul] at h
  change f.val combination = (3/2:ℂ) • f.val C4 at h
  exact h

end Cao
end
end Physics.ScalarCompletenessChecks
