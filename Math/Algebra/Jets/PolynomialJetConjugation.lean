import Math.Algebra.Jets.JetConjugation
import Math.Algebra.Jets.TwoSidedDifferentialRelations
import Math.RepresentationTheory.Jets.JetFunctor

namespace Math.PolynomialJetConjugation
set_option autoImplicit false
noncomputable section
open MvPolynomial ScalarJetAlgebra
variable {S I : Type*}

def conjugation : ScalarJetAlgebra.Algebra S I →ₛₗ[starRingEnd ℂ]
    ScalarJetAlgebra.Algebra S I where
  toFun := MvPolynomial.map (starRingEnd ℂ)
  map_add' := map_add _
  map_smul' c p := by simp [MvPolynomial.smul_eq_C_mul]

@[simp] theorem conjugation_X (j : Index S I) : conjugation (X j) = X j := by
  simp [conjugation]
@[simp] theorem conjugation_C (c : ℂ) : (conjugation (C c) : Algebra S I) = C (star c) := by
  simp [conjugation]
@[simp] theorem conjugation_mul (p q : Algebra S I) :
    conjugation (p*q) = conjugation p*conjugation q := map_mul (MvPolynomial.map _) _ _
@[simp] theorem involutive (p : Algebra S I) : conjugation (conjugation p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p j hp => simp [hp]

theorem derivative (i : I) (p : Algebra S I) :
    conjugation (totalDerivative i p) = totalDerivative i (conjugation p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add,hp,hq]
  | mul_X p j hp => simp only [totalDerivative_mul,totalDerivative_X,
      map_add,conjugation_mul,conjugation_X,hp]

theorem linearForm (v : JetLinear.Jet S I) :
    conjugation (JetLinear.linearForm v) = JetLinear.linearForm (JetConjugation.coefficients v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add,hv,hw]
  | single j c => simp [JetLinear.linearForm,map_smulₛₗ]

theorem naturality (L : JetLinear.Jet S I →ₗ[ℂ] JetLinear.Jet S I)
    (h : ∀ v, JetConjugation.coefficients (L v) = L (JetConjugation.coefficients v))
    (p : Algebra S I) : conjugation (JetFunctor.polynomialMap L p) =
      JetFunctor.polynomialMap L (conjugation p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    simp only [map_mul,conjugation_mul,conjugation_X,JetFunctor.polynomialMap_X,hp]
    rw [linearForm,h,JetConjugation.coefficients_single,star_one]
end
end Math.PolynomialJetConjugation
