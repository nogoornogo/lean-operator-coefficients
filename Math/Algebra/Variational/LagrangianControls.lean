import Math.RepresentationTheory.Lagrangian.BosonicLagrangianInput
import Math.LinearAlgebra.Exterior.ExteriorLeftDerivative

/-! Compiled use of the helper: users enter interactions and call a factory;
the following identities check the generated equations against known formulas. -/
namespace Math.LagrangianControls
set_option autoImplicit false
noncomputable section
open LocalPolynomial
open LocalPolynomial.Expr

abbrev ScalarExpr := Expr Empty Unit (Fin 4)
def phi : ScalarExpr := boson ()
def d (p : ScalarExpr) : ScalarExpr := derivative 0 p
def potential (g : ℂ) : ScalarExpr := (-g/6) • phi^6
def derivativeInteraction : ScalarExpr := phi^2 * (d phi)^2
def higherDerivative : ScalarExpr := (1/2 : ℂ) • (d (d phi))^2

/-- Adding an interaction requires an expression change and one factory call. -/
def scalarModel (g : ℂ) := ((1/2 : ℂ) • (d phi)^2 + potential g).scalarTrivialInput
def extendedScalarModel (g : ℂ) :=
  ((1/2 : ℂ) • (d phi)^2 + potential g + derivativeInteraction).scalarTrivialInput

abbrev field := (MvPolynomial.X ((), (0 : Fin 4 →₀ ℕ)) : Scalar Unit (Fin 4))
abbrev ds (p : Scalar Unit (Fin 4)) := ScalarJetAlgebra.totalDerivative 0 p

theorem potential_euler (g : ℂ) : (potential g).scalarEuler () = -g • field^5 := by
  have hc : (MvPolynomial.C (-1/6 : ℂ) : Scalar Unit (Fin 4))*6 = -1 := by
    have he : (-1/6 : ℂ)*6 = -1 := by norm_num
    simpa only [map_mul, map_ofNat, map_neg, map_one] using
      congrArg (fun c => (MvPolynomial.C c : Scalar Unit (Fin 4))) he
  simp [potential, phi, boson, Expr.smul_def, Expr.scalarEuler, Expr.euler, linearize, eulerTerms,
    Expr.eval, twist, VariationalIBP.adjoint, wordIndex,
    scalarProjection_even, map_mul, map_add]
  have hcoef : (MvPolynomial.C (-g/6) : Scalar Unit (Fin 4)) =
      MvPolynomial.C g * MvPolynomial.C (-1/6 : ℂ) := by
    rw [← map_mul]
    congr 1
    ring
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, hcoef]
  linear_combination (MvPolynomial.C g * field^5) * hc

theorem zero_euler : (0 : ScalarExpr).euler = 0 := rfl

theorem derivative_interaction_euler : derivativeInteraction.scalarEuler () =
    -2*field*(ds field)^2 - 2*field^2*ds (ds field) := by
  simp [derivativeInteraction, d, phi, boson, Expr.derivative,
    Expr.scalarEuler, Expr.euler, linearize, eulerTerms, Expr.eval, twist,
    VariationalIBP.adjoint, wordIndex, scalarProjection_derivative,
    ScalarJetAlgebra.totalDerivative_X,
    ScalarJetAlgebra.shift, ds]
  ring

theorem higher_derivative_euler : higherDerivative.scalarEuler () = ds (ds (ds (ds field))) := by
  have hc : (MvPolynomial.C (1/2 : ℂ) : Scalar Unit (Fin 4))*2 = 1 := by
    have he : (1/2 : ℂ)*2 = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg (fun c => (MvPolynomial.C c : Scalar Unit (Fin 4))) he
  simp [higherDerivative, d, phi, boson, Expr.derivative, Expr.smul_def,
    Expr.scalarEuler, Expr.euler, linearize, eulerTerms, Expr.eval, twist,
    VariationalIBP.adjoint, wordIndex, scalarProjection_derivative,
    ScalarJetAlgebra.totalDerivative_X,
    ScalarJetAlgebra.shift, ds]
  have hd := congrArg (fun q : Scalar Unit (Fin 4) => q * ds (ds (ds (ds field)))) hc
  simp only [ds, ScalarJetAlgebra.totalDerivative_X, ScalarJetAlgebra.shift, one_div, zero_add] at hd
  linear_combination hd

theorem total_derivative_euler : (d (phi^2)).scalarEuler () = 0 := by
  simp [d, phi, boson, Expr.derivative, Expr.scalarEuler, Expr.euler,
    linearize, eulerTerms, Expr.eval, twist, VariationalIBP.adjoint, wordIndex,
    scalarProjection_derivative,
    ScalarJetAlgebra.totalDerivative_X, ScalarJetAlgebra.shift]

theorem scalar_update (g : ℂ) :
    ((1/2 : ℂ) • (d phi)^2 + potential g + derivativeInteraction).scalarEuler () =
      ((1/2 : ℂ) • (d phi)^2 + potential g).scalarEuler () + derivativeInteraction.scalarEuler () :=
  Expr.scalarEuler_add _ _ _

abbrev MixedExpr := Expr Bool Unit Unit
@[reducible] local instance : AddCommGroup (A Bool Unit Unit) := inferInstance
@[reducible] local instance : Module ℂ (A Bool Unit Unit) := inferInstance
@[reducible] local instance : Ring (A Bool Unit Unit) := inferInstance

def psi (b : Bool) : MixedExpr := fermion b
def h : MixedExpr := boson ()
def yukawa (g : ℂ) : MixedExpr := g • (h * psi false * psi true)
def mixedModel (g : ℂ) := (yukawa g).trivialInput

theorem yukawa_even_euler (g : ℂ) :
    (yukawa g).euler (.inr ()) = g • ((psi false).eval * (psi true).eval) := by
  simp [yukawa, h, psi, fermion, boson, Expr.smul_def, Expr.euler, linearize, eulerTerms,
    Expr.eval, twist, VariationalIBP.adjoint, Algebra.smul_def]

theorem yukawa_first_odd_euler (g : ℂ) :
    (yukawa g).euler (.inl false) = g • (h.eval * (psi true).eval) := by
  simp [yukawa, h, psi, fermion, boson, Expr.smul_def, Expr.euler, linearize, eulerTerms,
    Expr.eval, twist, VariationalIBP.adjoint, Algebra.smul_def]

theorem yukawa_second_odd_euler (g : ℂ) :
    (yukawa g).euler (.inl true) = -g • (h.eval * (psi false).eval) := by
  simp [yukawa, h, psi, fermion, boson, Expr.smul_def, Expr.euler, linearize, eulerTerms,
    Expr.eval, twist, VariationalIBP.adjoint, Algebra.smul_def,
    TensorProduct.neg_tmul, neg_mul]

theorem odd_square_euler (b : Bool) : (psi b * psi b).euler = 0 := by
  classical
  ext s
  simp [psi, fermion, Expr.euler, linearize, eulerTerms, Expr.eval, twist,
    VariationalIBP.adjoint]

theorem odd_square_eval (b : Bool) : (psi b * psi b).eval = 0 := by
  simpa only [Expr.eval_mul, psi, fermion, Expr.eval, wordIndex, pow_two] using
    MixedJetAlgebra.odd_square (B := Unit) (I := Unit) (b, 0)

/-- The generated odd coefficients use the actual left Grassmann convention. -/
theorem yukawa_left_derivative (g : ℂ) (b : Bool) :
    TensorProduct.map
      (ExteriorLeftDerivative.derivative (Finsupp.lapply (b, (0 : Unit →₀ ℕ))))
      (LinearMap.id : MixedJetAlgebra.Even Unit Unit →ₗ[ℂ] _) (yukawa g).eval =
        (yukawa g).euler (.inl b) := by
  cases b
  · rw [yukawa_first_odd_euler]
    simp [yukawa, Expr.eval_smul, psi, h, Expr.fermion, Expr.boson,
      Expr.eval, wordIndex, MixedJetAlgebra.odd, MixedJetAlgebra.even,
      Algebra.TensorProduct.tmul_mul_tmul, ExteriorLeftDerivative.derivative,
      CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι,
      TensorProduct.smul_tmul']
  · rw [yukawa_second_odd_euler]
    simp [yukawa, Expr.eval_smul, psi, h, Expr.fermion, Expr.boson,
      Expr.eval, wordIndex, MixedJetAlgebra.odd, MixedJetAlgebra.even,
      Algebra.TensorProduct.tmul_mul_tmul, ExteriorLeftDerivative.derivative,
      CliffordAlgebra.contractLeft_ι_mul, CliffordAlgebra.contractLeft_ι,
      TensorProduct.smul_tmul', neg_smul]
    rfl

theorem odd_reordering_euler :
    (psi false*psi true).euler = (-(psi true*psi false)).euler := by
  classical
  ext s
  cases s with
  | inl b => cases b <;> simp [psi, fermion, Expr.euler, linearize,
      eulerTerms, Expr.eval, twist, VariationalIBP.adjoint,
      TensorProduct.neg_tmul, ← Algebra.TensorProduct.one_def]
  | inr b => simp [psi, fermion, Expr.euler, linearize,
      eulerTerms, Expr.eval, twist, VariationalIBP.adjoint]

theorem mixed_extraction (g : ℂ) (f : (mixedModel g).Coefficient) (u : A Bool Unit Unit) :
    (mixedModel g).coefficientEquiv f ((mixedModel g).projection u) = f.val u := rfl

end
end Math.LagrangianControls
