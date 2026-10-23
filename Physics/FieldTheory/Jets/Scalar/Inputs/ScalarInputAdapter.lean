import Math.RepresentationTheory.Jets.JetInputAdapter
import Physics.FieldTheory.Jets.Scalar.Inputs.PolynomialScalarEOM

/-! Actual interacting scalar equations through the additive relation/Hom input.
No Lagrangian or homogeneous EOM premise is supplied. -/
namespace Physics.ScalarInputAdapter
set_option autoImplicit false
noncomputable section
open Math Representation PolynomialScalarEOM

abbrev action : Representation ℂ Unit OffShell := trivial ℂ Unit OffShell

theorem stable (lambda : ℂ) : ∀ h : Unit, DifferentialEquation.combined D (equations lambda) ≤
    (DifferentialEquation.combined D (equations lambda)).comap (action h) :=
  fun _ _ hp => hp

abbrev Input (lambda : ℂ) := JetInputAdapter.EquationInput D (equations lambda) action

def equiv (lambda : ℂ) := JetInputAdapter.equationEquiv D (equations lambda) action (stable lambda)

theorem admissible_iff (lambda : ℂ) (f : IntertwiningMap action (trivial ℂ Unit ℂ)) :
    f ∈ Input lambda ↔ (∀ p ∈ ideal lambda, f p = 0) ∧ ∀ i p, f (D i p) = 0 :=
  JetInputAdapter.equation_admissible_iff _ _ _ _

@[simp] theorem extraction (lambda : ℂ) (f : Input lambda) (p : OffShell) :
    equiv lambda f (integrated lambda p) = f.val p := rfl

@[simp] theorem reconstruction (lambda : ℂ) (f : _) (p : OffShell) :
    ((equiv lambda).symm f).val p = f (integrated lambda p) := rfl

theorem interaction_constraint (lambda : ℂ) (f : Input lambda) :
    f.val LorentzJetIBP.waveField + lambda * f.val (field ^ 3) = 0 := by
  have hs : f.val (seed lambda) = 0 :=
    ((admissible_iff lambda f.val).mp f.property).1 _
      (DifferentialEquation.seed_mem _ _ (Set.mem_singleton _))
  change f.val (LorentzJetIBP.waveField + MvPolynomial.C lambda * field ^ 3) = 0 at hs
  rw [map_add, ← MvPolynomial.smul_eq_C_mul, map_smul] at hs
  exact hs

theorem nonzero_iff (lambda : ℂ) : (∃ f : Input lambda, f ≠ 0) ↔
    ∃ f : IntertwiningMap
      (action.quotient (DifferentialEquation.combined D (equations lambda)) (stable lambda))
      (trivial ℂ Unit ℂ), f ≠ 0 :=
  JetInputAdapter.nonzero_iff _ _ _ _

/-- The existing actual algebraic spin action, including its direction mixing. -/
abbrev lorentzAction : Representation ℂ LorentzDirections.Group OffShell :=
  JetFunctor.polynomialAction
    (JetDirections.combined LorentzJetIBP.scalarField LorentzDirections.direction)

theorem lorentz_stable (lambda : ℂ) : ∀ g, DifferentialEquation.combined D (equations lambda) ≤
    (DifferentialEquation.combined D (equations lambda)).comap (lorentzAction g) := by
  intro g
  exact DifferentialEquation.combined_map_stable D (equations lambda) (offAction g)
    (ideal_invariant lambda g)
    (fun i j => (LorentzDirections.direction g (Finsupp.single i 1)) j)
    (derivative_covariance g)

abbrev LorentzInput (lambda : ℂ) := JetInputAdapter.EquationInput D (equations lambda) lorentzAction

def lorentzEquiv (lambda : ℂ) :=
  JetInputAdapter.equationEquiv D (equations lambda) lorentzAction (lorentz_stable lambda)

@[simp] theorem lorentz_extraction (lambda : ℂ) (f : LorentzInput lambda) (p : OffShell) :
    lorentzEquiv lambda f (integrated lambda p) = f.val p := rfl

theorem lorentz_interaction_constraint (lambda : ℂ) (f : LorentzInput lambda) :
    f.val LorentzJetIBP.waveField + lambda * f.val (field ^ 3) = 0 := by
  have hs : f.val (seed lambda) = 0 :=
    ((JetInputAdapter.equation_admissible_iff D (equations lambda) lorentzAction f.val).mp f.property).1 _
      (DifferentialEquation.seed_mem _ _ (Set.mem_singleton _))
  change f.val (LorentzJetIBP.waveField + MvPolynomial.C lambda * field ^ 3) = 0 at hs
  rw [map_add, ← MvPolynomial.smul_eq_C_mul, map_smul] at hs
  exact hs

end
end Physics.ScalarInputAdapter
