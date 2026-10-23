import Math.RepresentationTheory.Jets.NonlinearJetIBP
import Physics.FieldTheory.Jets.Scalar.Inputs.MasslessScalarEOM

/-! A specified polynomial scalar equation with all ordinary descendants.
No analytic Euler–Lagrange or interacting Hilbert-series claim is made. -/
namespace Physics.PolynomialScalarEOM
set_option autoImplicit false
noncomputable section
open Math MvPolynomial

abbrev OffShell := ScalarJetAlgebra.Algebra Unit (Fin 4)
abbrev D := ScalarJetAlgebra.totalDerivative (S := Unit) (I := Fin 4)
abbrev field := MasslessScalarEOM.field

def seed (lambda : ℂ) : OffShell := LorentzJetIBP.waveField + C lambda * field ^ 3
def equations (lambda : ℂ) : Set OffShell := {seed lambda}
abbrev ideal (lambda : ℂ) := DifferentialEquation.ideal D (equations lambda)
abbrev Shell (lambda : ℂ) := DifferentialEquation.Shell D (equations lambda)
abbrev projection (lambda : ℂ) := DifferentialEquation.projection D (equations lambda)
abbrev integrated (lambda : ℂ) := DifferentialEquation.integrated D (equations lambda)

theorem seed_zero (lambda : ℂ) : projection lambda (seed lambda) = 0 :=
  (DifferentialEquation.projection_eq_zero _ _ _).mpr
    (DifferentialEquation.seed_mem _ _ (Set.mem_singleton _))

theorem descendants_zero (lambda : ℂ) (w : List (Fin 4)) :
    projection lambda (DifferentialEquation.word D w (seed lambda)) = 0 :=
  (DifferentialEquation.projection_eq_zero _ _ _).mpr
    (DifferentialEquation.descendant_mem _ _ w (Set.mem_singleton _))

theorem zeroEvaluation_seed (lambda : ℂ) : ScalarJetAlgebra.zeroEvaluation (seed lambda) = 0 := by
  simp [seed, MasslessScalarEOM.waveField_formula, MasslessScalarEOM.field]

theorem unit_survives (lambda : ℂ) : projection lambda 1 ≠ 0 := by
  rw [ne_eq, DifferentialEquation.projection_eq_zero]
  apply DifferentialEquation.one_not_mem _ _ ScalarJetAlgebra.zeroEvaluation
  · intro p hp
    rw [Set.mem_singleton_iff.mp hp]
    exact zeroEvaluation_seed lambda
  · exact ScalarJetAlgebra.zeroEvaluation_derivative

def offAction (g : LorentzDirections.Group) : OffShell →ₐ[ℂ] OffShell :=
  JetFunctor.polynomialMap
    (JetDirections.combined LorentzJetIBP.scalarField LorentzDirections.direction g)

theorem field_invariant (g : LorentzDirections.Group) : offAction g field = field := by
  rw [show field = JetLinear.linearForm (JetLinear.atOrder 0 (Finsupp.single () 1)) by
    simp [field, MasslessScalarEOM.field, JetLinear.linearForm]]
  rw [offAction, JetFunctor.polynomialMap_linearForm, JetDirections.combined_zero]
  rfl

theorem seed_invariant (lambda : ℂ) (g : LorentzDirections.Group) :
    offAction g (seed lambda) = seed lambda := by
  simp only [seed, map_add, map_mul, map_pow, MvPolynomial.algHom_C,
    MvPolynomial.algebraMap_eq, field_invariant]
  rw [show offAction g LorentzJetIBP.waveField = LorentzJetIBP.waveField from
    LorentzJetIBP.waveField_invariant g]

theorem ideal_invariant (lambda : ℂ) (g : LorentzDirections.Group) :
    ∀ p ∈ ideal lambda, offAction g p ∈ ideal lambda := by
  apply DifferentialEquation.map_stable
  · intro p hp
    rw [Set.mem_singleton_iff.mp hp, seed_invariant]
    exact DifferentialEquation.seed_mem _ _ (Set.mem_singleton _)
  · intro i p hp
    have h := JetFunctor.polynomial_covariant
      (JetDirections.combined LorentzJetIBP.scalarField LorentzDirections.direction)
      g i (fun j => (LorentzDirections.direction g (Finsupp.single i 1)) j)
      (JetDirections.combined_covariant _ _ g i) p
    change offAction g (D i p) = ∑ j, _ • D j (offAction g p) at h
    rw [h]
    exact Submodule.sum_mem _ (fun j _ => (DifferentialEquation.relations D (equations lambda)).smul_mem _
      (DifferentialEquation.stable _ _ j hp))

def lorentzTransport (lambda : ℂ) (g : LorentzDirections.Group) :=
  DifferentialEquation.transport D (equations lambda) (offAction g) (ideal_invariant lambda g)

theorem derivative_covariance (g : LorentzDirections.Group) (i : Fin 4) (p : OffShell) :
    offAction g (D i p) = ∑ j, (LorentzDirections.direction g (Finsupp.single i 1)) j •
      D j (offAction g p) :=
  JetFunctor.polynomial_covariant
    (JetDirections.combined LorentzJetIBP.scalarField LorentzDirections.direction)
    g i _ (JetDirections.combined_covariant _ _ g i) p

def lorentzIBPTransport (lambda : ℂ) (g : LorentzDirections.Group) :=
  DifferentialEquation.integratedTransport D (equations lambda) (offAction g)
    (ideal_invariant lambda g)
    (fun i j => (LorentzDirections.direction g (Finsupp.single i 1)) j)
    (derivative_covariance g)

def finiteImage (lambda : ℂ) (n d : ℕ) := DifferentialEquation.image D (equations lambda)
  (ScalarJetAlgebra.grade (S := Unit) (I := Fin 4) n d)

instance finiteImage_finite (lambda : ℂ) (n d : ℕ) : FiniteDimensional ℂ (finiteImage lambda n d) := by
  unfold finiteImage
  infer_instance

def sourceEquiv (lambda : ℂ) := DifferentialEquation.sourceEquiv D (equations lambda)
def coefficientEquiv (lambda : ℂ) := DifferentialEquation.coefficientEquiv (W := ℂ) D (equations lambda)

theorem kinetic_relation (lambda : ℂ) :
    LorentzJetIBP.kinetic - C lambda * field ^ 4 ∈ DifferentialEquation.combined D (equations lambda) := by
  have he : field * seed lambda ∈ ideal lambda :=
    (ideal lambda).mul_mem_left _ (DifferentialEquation.seed_mem _ _ (Set.mem_singleton _))
  have hd : LorentzJetIBP.kinetic + field * LorentzJetIBP.waveField ∈ DifferentialEquation.ibp D := by
    rw [← MasslessScalarEOM.divergence_current]
    exact Submodule.sum_mem _ (fun i _ => DifferentialEquation.derivative_mem_ibp D i _)
  have h : LorentzJetIBP.kinetic - C lambda * field ^ 4 =
      (LorentzJetIBP.kinetic + field * LorentzJetIBP.waveField) - field * seed lambda := by
    dsimp [seed]
    ring
  rw [h]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right hd) (Submodule.mem_sup_left he)

theorem kinetic_mod_ibp (lambda : ℂ) :
    integrated lambda LorentzJetIBP.kinetic = lambda • integrated lambda (field ^ 4) := by
  have h := (Submodule.Quotient.mk_eq_zero _).mpr (kinetic_relation lambda)
  change integrated lambda (LorentzJetIBP.kinetic - C lambda * field ^ 4) = 0 at h
  rw [map_sub, C_mul', map_smul] at h
  exact sub_eq_zero.mp h

end
end Physics.PolynomialScalarEOM
