import Math.Algebra.Constructions.ScalarZeroDerivative
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarConstantCoefficients

/-! Complete degree-zero selected image in the full free scalar EOM/IBP
quotient. The separating functional is globally Lorentz invariant. -/
namespace Physics.ScalarZeroDerivativeCertificate
set_option autoImplicit false
noncomputable section
open Math PolynomialScalarEOM
abbrev P := ScalarDerivativeInterface.scalar 0
abbrev V (n : ℕ) := ScalarJetAlgebra.grade (S := Unit) (I := Fin 4) n 0
abbrev Image (n : ℕ) := P.selectedImage (V n)

def generator (n : ℕ) : Image n :=
  ⟨P.projection (ScalarZeroDerivative.monomialSource n 1).val,
    ⟨ScalarZeroDerivative.monomialSource n 1,rfl⟩⟩

def coordinate (n : ℕ) : Image n →ₗ[ℂ] ℂ :=
  (P.coefficientEquiv (ScalarConstantCoefficients.functional n)).toLinearMap.comp
    (P.selectedImage (V n)).subtype

theorem coordinate_generator (n : ℕ) : coordinate n (generator n) = 1 := by
  change (ScalarConstantCoefficients.functional n).val
    (ScalarZeroDerivative.monomialSource n 1).val = 1
  rw [ScalarZeroDerivative.generator_value]
  exact ScalarConstantCoefficients.detects n

theorem reconstruction (n : ℕ) (x : Image n) :
    x = coordinate n x • generator n := by
  obtain ⟨p,hp⟩ := x.property
  have hr : p.val = ScalarZeroDerivative.coordinate n p •
      (ScalarZeroDerivative.monomialSource n 1).val := by
    rw [ScalarZeroDerivative.reconstruction n p]
    simp [ScalarZeroDerivative.coordinate,ScalarZeroDerivative.monomialSource,
      MvPolynomial.smul_monomial]
  have hx : x = ScalarZeroDerivative.coordinate n p • generator n := by
    apply Subtype.ext
    change x.val = ScalarZeroDerivative.coordinate n p • P.projection _
    rw [← hp]
    change P.projection p.val = _
    rw [hr,map_smul]
  have hc := congrArg (coordinate n) hx
  rw [map_smul,coordinate_generator,smul_eq_mul,mul_one] at hc
  exact hx.trans (congrArg (fun c : ℂ => c • generator n) hc.symm)

def equivalence (n : ℕ) : Image n ≃ₗ[ℂ] ℂ where
  toLinearMap := coordinate n
  invFun c := c • generator n
  left_inv x := (reconstruction n x).symm
  right_inv c := by
    change coordinate n (c • generator n) = c
    rw [map_smul,coordinate_generator,smul_eq_mul,mul_one]

theorem dimension (n : ℕ) : Module.finrank ℂ (Image n) = 1 := by
  rw [(equivalence n).finrank_eq]
  exact Module.finrank_self ℂ

theorem four_scalar_dimension : Module.finrank ℂ (Image 4) = 1 := dimension 4
end
end Physics.ScalarZeroDerivativeCertificate
