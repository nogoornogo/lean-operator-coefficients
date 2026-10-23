import Math.Algebra.Constructions.ScalarEngineeringTwo
import Physics.FieldTheory.Jets.Scalar.Inputs.PolynomialScalarEOM
import Mathlib.Algebra.Polynomial.Coeff

/-! Complete engineering-degree-two image in the full nonlinear scalar EOM/IBP
source. A coefficient functional controls all unbounded relations. -/
namespace Physics.ScalarEngineeringClassification
set_option autoImplicit false
noncomputable section
open Math MvPolynomial
open PolynomialScalarEOM

def polynomialEvaluation : OffShell →ₐ[ℂ] Polynomial ℂ := by
  classical
  exact aeval (fun j => if j.2 = 0 then Polynomial.X else 0)

theorem evaluation_shift (i : Fin 4) (j : ScalarJetAlgebra.Index Unit (Fin 4)) :
    polynomialEvaluation (X (ScalarJetAlgebra.shift i j)) = 0 := by
  have h : j.2 + Finsupp.single i 1 ≠ 0 := by
    intro he
    have hi := congrArg (fun a : Fin 4 →₀ ℕ => a i) he
    simp at hi
  simp [polynomialEvaluation, ScalarJetAlgebra.shift, h]

theorem evaluation_derivative (i : Fin 4) (p : OffShell) : polynomialEvaluation (D i p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    rw [ScalarJetAlgebra.totalDerivative_mul, ScalarJetAlgebra.totalDerivative_X,
      map_add, map_mul, map_mul, hp, evaluation_shift]
    simp

theorem evaluation_seed (lambda : ℂ) :
    polynomialEvaluation (seed lambda) = Polynomial.C lambda * Polynomial.X ^ 3 := by
  simp [seed, MasslessScalarEOM.waveField_formula, field, MasslessScalarEOM.field, polynomialEvaluation]

def cubicIdeal : Ideal (Polynomial ℂ) := Ideal.span {Polynomial.X ^ 3}

theorem eom_evaluation_mem (lambda : ℂ) {p : OffShell} (hp : p ∈ ideal lambda) :
    polynomialEvaluation p ∈ cubicIdeal := by
  have hle : ideal lambda ≤ cubicIdeal.comap polynomialEvaluation.toRingHom := by
    apply DifferentialEquation.minimal
    · intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      change polynomialEvaluation (seed lambda) ∈ cubicIdeal
      rw [evaluation_seed]
      exact cubicIdeal.mul_mem_left _ (Ideal.subset_span (Set.mem_singleton _))
    · intro i p hp
      change polynomialEvaluation (D i p) ∈ cubicIdeal
      rw [evaluation_derivative]
      exact cubicIdeal.zero_mem
  exact hle hp

def coefficient : OffShell →ₗ[ℂ] ℂ := (Polynomial.lcoeff ℂ 2).comp polynomialEvaluation.toLinearMap

theorem coefficient_eom (lambda : ℂ) {p : OffShell} (hp : p ∈ ideal lambda) : coefficient p = 0 := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (eom_evaluation_mem lambda hp)
  change (polynomialEvaluation p).coeff 2 = 0
  rw [← hq, Polynomial.coeff_mul_X_pow']
  norm_num

theorem coefficient_derivative (i : Fin 4) (p : OffShell) : coefficient (D i p) = 0 := by
  change (polynomialEvaluation (D i p)).coeff 2 = 0
  rw [evaluation_derivative, Polynomial.coeff_zero]

theorem combined_le_kernel (lambda : ℂ) :
    DifferentialEquation.combined D (equations lambda) ≤ coefficient.ker := by
  apply sup_le
  · exact fun p hp => coefficient_eom lambda hp
  · rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c e hc he => simpa only [map_add] using coefficient.ker.add_mem hc he
    | single i p =>
      rw [DifferentialEquation.divergence_single]
      exact coefficient_derivative i p

def quotientCoefficient (lambda : ℂ) :=
  (DifferentialEquation.combined D (equations lambda)).liftQ coefficient (combined_le_kernel lambda)

theorem coefficient_square : coefficient (PolynomialScalarEOM.field ^ 2) = 1 := by
  change (polynomialEvaluation (PolynomialScalarEOM.field ^ 2)).coeff 2 = 1
  simp [polynomialEvaluation, PolynomialScalarEOM.field, MasslessScalarEOM.field]

theorem square_survives (lambda : ℂ) : integrated lambda (PolynomialScalarEOM.field ^ 2) ≠ 0 := by
  intro h
  have he := congrArg (quotientCoefficient lambda) h
  change coefficient (PolynomialScalarEOM.field ^ 2) = 0 at he
  rw [coefficient_square] at he
  exact one_ne_zero he

abbrev Source := ScalarEngineeringTwo.Source (Fin 4)
def image (lambda : ℂ) := JetEngineering.ibpImage (equations lambda) 2
def sourceProjection (lambda : ℂ) : Source →ₗ[ℂ] image lambda where
  toFun p := ⟨integrated lambda p.val, ⟨p.val, p.property, rfl⟩⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem sourceProjection_surjective (lambda : ℂ) : Function.Surjective (sourceProjection lambda) := by
  rintro ⟨_, p, hp, rfl⟩
  exact ⟨⟨p, hp⟩, rfl⟩

def generator (lambda : ℂ) := sourceProjection lambda ScalarEngineeringTwo.square

theorem first_zero (lambda : ℂ) (i : Fin 4) : sourceProjection lambda (ScalarEngineeringTwo.first i) = 0 := by
  apply Subtype.ext
  change integrated lambda (X ((), Finsupp.single i 1)) = 0
  have h := DifferentialEquation.integrated_derivative D (equations lambda) i PolynomialScalarEOM.field
  simpa [PolynomialScalarEOM.field, MasslessScalarEOM.field, ScalarJetAlgebra.shift] using h

theorem reconstruction (lambda : ℂ) (p : Source) :
    sourceProjection lambda p = p.val.coeff (Finsupp.single ScalarEngineeringTwo.zeroIndex 2) • generator lambda := by
  conv_lhs => rw [ScalarEngineeringTwo.source_reconstruct p]
  simp only [map_add, map_smul, map_sum, first_zero, smul_zero, Finset.sum_const_zero, add_zero, generator]

theorem generator_nonzero (lambda : ℂ) : generator lambda ≠ 0 := by
  intro h
  apply square_survives lambda
  have he := congrArg Subtype.val h
  simpa [generator, sourceProjection, ScalarEngineeringTwo.square, ← X_pow_eq_monomial,
    ScalarEngineeringTwo.zeroIndex, PolynomialScalarEOM.field, MasslessScalarEOM.field] using he

def coordinate (lambda : ℂ) : image lambda →ₗ[ℂ] ℂ :=
  (quotientCoefficient lambda).comp (image lambda).subtype

theorem coordinate_generator (lambda : ℂ) : coordinate lambda (generator lambda) = 1 := by
  change coefficient (monomial (Finsupp.single ScalarEngineeringTwo.zeroIndex 2) 1) = 1
  simpa [PolynomialScalarEOM.field, MasslessScalarEOM.field, X_pow_eq_monomial,
    ScalarEngineeringTwo.zeroIndex] using coefficient_square

def equivalence (lambda : ℂ) : image lambda ≃ₗ[ℂ] ℂ where
  toLinearMap := coordinate lambda
  invFun c := c • generator lambda
  left_inv p := by
    obtain ⟨p, rfl⟩ := sourceProjection_surjective lambda p
    change coordinate lambda (sourceProjection lambda p) • generator lambda = sourceProjection lambda p
    rw [reconstruction]
    simp only [map_smul, coordinate_generator, smul_eq_mul, mul_one]
  right_inv c := by
    change coordinate lambda (c • generator lambda) = c
    simp only [map_smul, coordinate_generator, smul_eq_mul, mul_one]

def basis (lambda : ℂ) : Module.Basis Unit ℂ (image lambda) :=
  (Module.Basis.singleton Unit ℂ).map (equivalence lambda).symm

theorem dimension (lambda : ℂ) : Module.finrank ℂ (image lambda) = 1 := by
  rw [(equivalence lambda).finrank_eq]
  exact Module.finrank_self ℂ

end
end Physics.ScalarEngineeringClassification
