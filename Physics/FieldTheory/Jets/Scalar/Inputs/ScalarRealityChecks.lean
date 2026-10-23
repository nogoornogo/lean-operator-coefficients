import Math.Algebra.Jets.PolynomialJetConjugation
import Math.Algebra.Jets.SemilinearDifferentialRelations
import Math.LinearAlgebra.Selection.HermitianCoefficientChecks
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarZeroDerivativeCertificate
import Physics.FieldTheory.Jets.Weyl.Equations.WeylJetAdjoint

/-! Supported reality checks on actual scalar and paired on-shell sources. -/
namespace Physics.ScalarRealityChecks
set_option autoImplicit false
noncomputable section
open Math PolynomialScalarEOM PolynomialJetConjugation

abbrev T (lambda : ℂ) := (ScalarDerivativeInterface.scalar lambda).relations

theorem seed_conjugate (lambda : ℂ) : conjugation (seed lambda) = seed (star lambda) := by
  simp [seed,MasslessScalarEOM.waveField_formula,field,MasslessScalarEOM.field,
    PolynomialJetConjugation.conjugation]

theorem stable (lambda : ℝ) : T lambda ≤ (T lambda).comap conjugation := by
  rw [show T lambda = TwoSidedDifferential.combined (fun i => (D i).toLinearMap)
    (equations lambda) from (TwoSidedDifferential.commutative_combined D (equations lambda)).symm]
  apply SemilinearDifferentialRelations.stable
  · exact conjugation_mul
  · exact derivative
  · intro p hp
    rw [Set.mem_singleton_iff.mp hp,seed_conjugate]
    exact TwoSidedDifferential.seed_mem _ _ (by simp [equations])

def adjoint (lambda : ℝ) : (ScalarDerivativeInterface.scalar lambda).Source →ₛₗ[starRingEnd ℂ]
    (ScalarDerivativeInterface.scalar lambda).Source :=
  (T lambda).mapQ _ conjugation (stable lambda)

@[simp] theorem adjoint_projection (lambda : ℝ) (p : OffShell) :
    adjoint lambda ((ScalarDerivativeInterface.scalar lambda).projection p) =
      (ScalarDerivativeInterface.scalar lambda).projection (conjugation p) := rfl

theorem adjoint_involutive (lambda : ℝ) (x : (ScalarDerivativeInterface.scalar lambda).Source) :
    adjoint lambda (adjoint lambda x) = x := by
  obtain ⟨p,rfl⟩ := (T lambda).mkQ_surjective x
  change adjoint lambda (adjoint lambda
    ((ScalarDerivativeInterface.scalar lambda).projection p)) =
      (ScalarDerivativeInterface.scalar lambda).projection p
  rw [adjoint_projection,adjoint_projection,involutive]

theorem conjugation_action (g : LorentzDirections.Group) (p : OffShell) :
    conjugation (offAction g p) = offAction g (conjugation p) := by
  apply PolynomialJetConjugation.naturality
  intro v
  rw [show JetDirections.combined LorentzJetIBP.scalarField LorentzDirections.direction g =
      JetDirections.jetMap (S := Unit) (LorentzDirections.direction g) from
    JetDirections.combined_trivial LorentzDirections.direction g]
  exact JetConjugation.coefficients_direction _ (ConjugateWeylEquation.direction_real g) v

theorem adjoint_action (lambda : ℝ) (g : LorentzDirections.Group)
    (x : (ScalarDerivativeInterface.scalar lambda).Source) :
    adjoint lambda ((ScalarDerivativeInterface.scalar lambda).residual g x) =
      (ScalarDerivativeInterface.scalar lambda).residual g (adjoint lambda x) := by
  obtain ⟨p,rfl⟩ := (T lambda).mkQ_surjective x
  change (T lambda).mkQ (conjugation (offAction g p)) =
    (T lambda).mkQ (offAction g (conjugation p))
  rw [conjugation_action]

theorem power_fixed (lambda : ℝ) (n : ℕ) :
    adjoint lambda ((ScalarDerivativeInterface.scalar lambda).projection (field^n)) =
      (ScalarDerivativeInterface.scalar lambda).projection (field^n) := by
  rw [adjoint_projection]
  congr 1
  simp [field,MasslessScalarEOM.field,PolynomialJetConjugation.conjugation]

theorem free_power_real_iff (n : ℕ) (c : ℂ) :
    adjoint 0 (c • (ScalarDerivativeInterface.scalar 0).projection (field^n)) =
      c • (ScalarDerivativeInterface.scalar 0).projection (field^n) ↔ c.im = 0 := by
  have hf := power_fixed 0 n
  change adjoint 0 ((ScalarDerivativeInterface.scalar 0).projection (field^n)) =
    (ScalarDerivativeInterface.scalar 0).projection (field^n) at hf
  rw [map_smulₛₗ,hf]
  constructor
  · intro h
    have he := congrArg
      ((ScalarDerivativeInterface.scalar 0).coefficientEquiv (ScalarConstantCoefficients.functional n)) h
    rw [map_smul,map_smul] at he
    change star c * (ScalarConstantCoefficients.functional n).val (field^n) =
      c * (ScalarConstantCoefficients.functional n).val (field^n) at he
    rw [ScalarConstantCoefficients.detects,mul_one,mul_one] at he
    exact Complex.conj_eq_iff_im.mp he
  · intro hc
    rw [show (starRingEnd ℂ) c = c from Complex.conj_eq_iff_im.mpr hc]

theorem image_fixed_iff (n : ℕ) (x : ScalarZeroDerivativeCertificate.Image n) :
    adjoint 0 x.val = x.val ↔ star (ScalarZeroDerivativeCertificate.coordinate n x) =
      ScalarZeroDerivativeCertificate.coordinate n x := by
  have hx : x.val = ScalarZeroDerivativeCertificate.coordinate n x •
      (ScalarDerivativeInterface.scalar 0).projection (field^n) := by
    have h := congrArg (fun y : ScalarZeroDerivativeCertificate.Image n => y.val)
      (ScalarZeroDerivativeCertificate.reconstruction n x)
    simpa [ScalarZeroDerivativeCertificate.generator,ScalarZeroDerivative.generator_value,
      field,MasslessScalarEOM.field] using h
  rw [hx]
  exact (free_power_real_iff n _).trans Complex.conj_eq_iff_im.symm

def realImage (n : ℕ) : Submodule ℝ (ScalarZeroDerivativeCertificate.Image n) :=
  HermitianCoefficientChecks.realLine.comap
    ((ScalarZeroDerivativeCertificate.equivalence n).toLinearMap.restrictScalars ℝ)

theorem realImage_iff (n : ℕ) (x : ScalarZeroDerivativeCertificate.Image n) :
    x ∈ realImage n ↔ adjoint 0 x.val = x.val := (image_fixed_iff n x).symm

def realImageEquiv (n : ℕ) : realImage n ≃ₗ[ℝ] HermitianCoefficientChecks.realLine where
  toFun x := ⟨ScalarZeroDerivativeCertificate.equivalence n x.val,x.property⟩
  invFun c := ⟨(ScalarZeroDerivativeCertificate.equivalence n).symm c.val,by
    change star ((ScalarZeroDerivativeCertificate.equivalence n)
      ((ScalarZeroDerivativeCertificate.equivalence n).symm c.val)) =
        (ScalarZeroDerivativeCertificate.equivalence n)
          ((ScalarZeroDerivativeCertificate.equivalence n).symm c.val)
    rw [LinearEquiv.apply_symm_apply]
    exact c.property⟩
  left_inv x := Subtype.ext ((ScalarZeroDerivativeCertificate.equivalence n).symm_apply_apply x.val)
  right_inv c := Subtype.ext ((ScalarZeroDerivativeCertificate.equivalence n).apply_symm_apply c.val)
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (((ScalarZeroDerivativeCertificate.equivalence n).toLinearMap.restrictScalars ℝ).map_smul a x.val)

theorem real_image_dimension (n : ℕ) : Module.finrank ℝ (realImage n) = 1 := by
  rw [(realImageEquiv n).finrank_eq]
  exact HermitianCoefficientChecks.real_line_dimension

/-- This source has already imposed both conjugate Weyl equation families. -/
theorem paired_weyl_involutive (x : WeylJetAdjoint.Source) :
    WeylJetAdjoint.sourceAdjoint (WeylJetAdjoint.sourceAdjoint x) = x :=
  WeylJetAdjoint.sourceAdjoint_involutive x

theorem paired_weyl_derivative (i : Fin 4) (p : WeylJetAdjoint.Algebra) :
    WeylJetAdjoint.adjoint (WeylJetAdjoint.derivative i p) =
      WeylJetAdjoint.derivative i (WeylJetAdjoint.adjoint p) :=
  WeylJetAdjoint.adjoint_derivative i p

theorem paired_weyl_action (g : WeylLinearEquation.Group) (p : WeylJetAdjoint.Algebra) :
    ExteriorAlgebra.map (WeylJetAdjoint.action g) (WeylJetAdjoint.adjoint p) =
      WeylJetAdjoint.adjoint (ExteriorAlgebra.map (WeylJetAdjoint.action g) p) :=
  WeylJetAdjoint.adjoint_action g p

/-- Conjugating a raw equation descendant still vanishes after both EOM families. -/
theorem paired_left_conjugate_zero (p : Math.JetDirections.Symbols (Fin 4))
    (f : WeylLinearEquation.Equations) :
    WeylJetAdjoint.algebraProjection (JetExteriorAdjoint.map WeylJetAdjoint.rawConjugation
      (ExteriorAlgebra.ι ℂ (LinearJetEquation.multiple p (WeylLinearEquation.seed f),0))) = 0 := by
  rw [WeylJetAdjoint.algebraProjection_adjoint,WeylJetAdjoint.left_descendant_zero,map_zero]
end
end Physics.ScalarRealityChecks
