import Math.Algebra.Variational.LagrangianControls
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarInputAdapter

/-! The optional compiler on the existing actual Lorentz scalar source.
The caller supplies a coupling; first variation and relation stability are
proved here once, rather than requested from each consumer. -/
namespace Physics.ScalarLagrangianHelper
set_option autoImplicit false
noncomputable section
open Math Math.LocalPolynomial.Expr PolynomialScalarEOM
open Math.LocalPolynomial hiding D

abbrev E := Expr Empty Unit (Fin 4)
abbrev phi : E := Expr.boson ()
def directionalKinetic (i : Fin 4) : E := (1/2 : ℂ) • (derivative i phi)^2
def kinetic : E := directionalKinetic 0 - directionalKinetic 1 - directionalKinetic 2 - directionalKinetic 3
def density (g : ℂ) : E := kinetic + LagrangianControls.potential g

theorem density_eval (g : ℂ) : (density g).scalarEval =
    (1/2 : ℂ) • LorentzJetIBP.kinetic - (g/6) • field^6 := by
  have hp : phi.scalarEval = field := by
    simp only [phi, Expr.boson, Expr.scalarEval, Expr.eval, wordIndex, scalarProjection_even]
    rfl
  simp only [density, kinetic, directionalKinetic, LagrangianControls.potential,
    LagrangianControls.phi, scalarEval_add, scalarEval_sub, scalarEval_smul,
    scalarEval_pow, scalarEval_derivative, hp]
  rw [LorentzJetIBP.kinetic_formula]
  simp only [field, MasslessScalarEOM.field, ScalarJetAlgebra.totalDerivative_X,
    ScalarJetAlgebra.shift, zero_add, smul_add, smul_neg, neg_div, neg_smul, sub_eq_add_neg]

theorem directional_euler (i : Fin 4) :
    (directionalKinetic i).scalarEuler () = -D i (D i field) := by
  have hs : ((derivative i phi)^2).scalarEuler () = -(2 : ℂ) • D i (D i field) := by
    simp [phi, Expr.derivative, Expr.boson, Expr.scalarEuler, Expr.euler, linearize,
      eulerTerms, Expr.eval, twist, VariationalIBP.adjoint, wordIndex,
      scalarProjection_derivative, ScalarJetAlgebra.totalDerivative_X,
      ScalarJetAlgebra.shift, field, MasslessScalarEOM.field, Algebra.smul_def,
      MvPolynomial.algebraMap_eq]
    simp only [map_ofNat]
    ring
  rw [directionalKinetic, scalarEuler_smul, hs, smul_smul]
  norm_num

theorem kinetic_euler : kinetic.scalarEuler () = -LorentzJetIBP.waveField := by
  simp only [kinetic, scalarEuler_sub, directional_euler]
  rw [MasslessScalarEOM.waveField_formula]
  simp only [D, ScalarJetAlgebra.totalDerivative_X, ScalarJetAlgebra.shift,
    field, MasslessScalarEOM.field, zero_add, ← Finsupp.single_add]
  abel

theorem generated_equation (g : ℂ) :
    (density g).scalarEuler () = -(LorentzJetIBP.waveField + g • field^5) := by
  rw [density, scalarEuler_add, kinetic_euler, LagrangianControls.potential_euler]
  change -LorentzJetIBP.waveField + -g • field^5 = -(LorentzJetIBP.waveField + g • field^5)
  rw [neg_smul, neg_add]

theorem generated_invariant (g : ℂ) (a : LorentzDirections.Group) :
    offAction a ((density g).scalarEuler ()) = (density g).scalarEuler () := by
  rw [generated_equation]
  simp only [map_neg, map_add, map_smul, map_pow, field_invariant]
  rw [show offAction a LorentzJetIBP.waveField = LorentzJetIBP.waveField from
    LorentzJetIBP.waveField_invariant a]

theorem ideal_stable (g : ℂ) (a : LorentzDirections.Group) :
    ∀ p ∈ DifferentialEquation.ideal D (density g).scalarSeeds,
      offAction a p ∈ DifferentialEquation.ideal D (density g).scalarSeeds := by
  apply DifferentialEquation.map_stable
  · rintro p ⟨b, rfl⟩
    cases b
    rw [generated_invariant]
    exact DifferentialEquation.seed_mem _ _ ⟨(), rfl⟩
  · intro i p hp
    rw [derivative_covariance]
    exact Submodule.sum_mem _ (fun j _ =>
      (DifferentialEquation.relations D (density g).scalarSeeds).smul_mem _
        (DifferentialEquation.stable D _ j hp))

theorem stable (g : ℂ) : ∀ a, DifferentialEquation.combined D (density g).scalarSeeds ≤
    (DifferentialEquation.combined D (density g).scalarSeeds).comap (ScalarInputAdapter.lorentzAction a) := by
  intro a
  exact DifferentialEquation.combined_map_stable D _ (offAction a) (ideal_stable g a)
    (fun i j => (LorentzDirections.direction a (Finsupp.single i 1)) j)
    (derivative_covariance a)

def input (g : ℂ) := (density g).scalarInput ScalarInputAdapter.lorentzAction (stable g)

theorem extraction (g : ℂ) (f : (input g).Coefficient) (p : OffShell) :
    (input g).coefficientEquiv f ((input g).projection p) = f.val p := rfl

theorem first_variation_zero (g : ℂ) (eta : OffShell) :
    (input g).projection
      (JetFirstVariation.variation (fun _ : Unit => eta) (density g).scalarEval) = 0 :=
  (density g).scalar_onShell_variation _

end
end Physics.ScalarLagrangianHelper
