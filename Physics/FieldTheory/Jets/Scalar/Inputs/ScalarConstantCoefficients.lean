import Math.RepresentationTheory.Jets.JetConstantProjection
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarProhibitionConditions

/-! Global Lorentz-equivariant functionals annihilating all free EOM and IBP.
These certify actual nonzero classes, not merely polynomial representatives. -/
namespace Physics.ScalarConstantCoefficients
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM JetConstantProjection

abbrev evaluation : OffShell →ₐ[ℂ] MvPolynomial Unit ℂ := constantJets
def coefficient (n : ℕ) : OffShell →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff ℂ (Finsupp.single () n)).comp evaluation.toLinearMap

theorem evaluation_ideal {p : OffShell} (hp : p ∈ ideal 0) : evaluation p = 0 := by
  have hle : ideal 0 ≤ (⊥ : Ideal (MvPolynomial Unit ℂ)).comap evaluation.toRingHom := by
    apply DifferentialEquation.minimal
    · rintro p hp
      rw [Set.mem_singleton_iff.mp hp]
      change evaluation (seed 0) = 0
      simp [seed,MasslessScalarEOM.waveField_formula,evaluation,constantJets_X]
    · intro i p hp
      change evaluation (D i p) = 0
      exact constantJets_derivative i p
  exact hle hp

theorem evaluation_invariant (g : LorentzDirections.Group) (p : OffShell) :
    evaluation (ScalarInputAdapter.lorentzAction g p) = evaluation p := by
  change constantJets (JetFunctor.polynomialMap
    (JetDirections.combined LorentzJetIBP.scalarField LorentzDirections.direction g) p) = _
  rw [show JetDirections.combined LorentzJetIBP.scalarField LorentzDirections.direction g =
      JetDirections.jetMap (S := Unit) (LorentzDirections.direction g) from
    JetDirections.combined_trivial LorentzDirections.direction g]
  exact constantJets_direction _ p

theorem coefficient_relations (n : ℕ) :
    DifferentialEquation.combined D (equations 0) ≤ (coefficient n).ker := by
  apply sup_le
  · intro p hp
    change (evaluation p).coeff (Finsupp.single () n) = 0
    rw [evaluation_ideal hp]
    simp
  · rintro _ ⟨c,rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simpa only [map_add] using (coefficient n).ker.add_mem hc hd
    | single i p =>
      rw [DifferentialEquation.divergence_single]
      change (evaluation (D i p)).coeff (Finsupp.single () n) = 0
      rw [constantJets_derivative]
      simp

def functional (n : ℕ) : (ScalarDerivativeInterface.scalar 0).Coefficient := ⟨{
  toLinearMap := coefficient n
  isIntertwining' g := by
    apply LinearMap.ext
    intro p
    change (evaluation (ScalarInputAdapter.lorentzAction g p)).coeff (Finsupp.single () n) = _
    rw [evaluation_invariant]
    rfl },fun _ hp => coefficient_relations n hp⟩

theorem detects (n : ℕ) : (functional n).val (field^n) = 1 := by
  change (evaluation (field^n)).coeff (Finsupp.single () n) = 1
  rw [map_pow]
  have he : evaluation field = X () := by
    change constantJets (X ((),0) : OffShell) = X ()
    rw [constantJets_X]
    simp
  rw [he]
  simp [X_pow_eq_monomial]

theorem nonzero (n : ℕ) : functional n ≠ 0 := by
  intro hz
  have he := congrArg (fun f : (ScalarDerivativeInterface.scalar 0).Coefficient => f.val (field^n)) hz
  rw [detects] at he
  exact one_ne_zero he

theorem cubic_value_iff (lambda c : ℂ) :
    (∃ f : (ScalarDerivativeInterface.scalar lambda).Coefficient, f.val (field^3) = c) ↔
      lambda*c = 0 := by
  constructor
  · rintro ⟨f,hf⟩
    rw [← hf]
    exact ScalarProhibitionConditions.cubic_constraint lambda f
  · intro hc
    by_cases hl : lambda = 0
    · subst lambda
      refine ⟨c • functional 3,?_⟩
      change c * (functional 3).val (field^3) = c
      rw [detects,mul_one]
    · have hz := (mul_eq_zero.mp hc).resolve_left hl
      exact ⟨0,hz.symm⟩

theorem nonzero_cubic_iff (lambda : ℂ) :
    (∃ f : (ScalarDerivativeInterface.scalar lambda).Coefficient, f.val (field^3) ≠ 0) ↔
      lambda = 0 := by
  constructor
  · exact ScalarProhibitionConditions.nonzero_cubic_requires_zero_coupling lambda
  · intro hl
    subst lambda
    exact ⟨functional 3,by rw [detects]; exact one_ne_zero⟩

end
end Physics.ScalarConstantCoefficients
