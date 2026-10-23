import Math.RepresentationTheory.Lagrangian.LagrangianInput
import Math.Algebra.Variational.JetFirstVariation

/-! The same expression compiler feeds the existing commutative equations
factory. Projection is used only for expressions with no odd field labels. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
open MixedJetAlgebra
open scoped TensorProduct
variable {F B I : Type*}
abbrev Scalar (B I : Type*) := ScalarJetAlgebra.Algebra B I

def scalarProjection : A F B I →ₐ[ℂ] Scalar B I :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId ℂ (Scalar B I)).comp ExteriorAlgebra.algebraMapInv)
    (AlgHom.id ℂ _) (fun _ _ => Commute.all _ _)

@[simp] theorem scalarProjection_tmul (x : Odd F I) (y : Even B I) :
    scalarProjection (x ⊗ₜ[ℂ] y) = MvPolynomial.C (ExteriorAlgebra.algebraMapInv x) * y := rfl

@[simp] theorem scalarProjection_even (j : ScalarJetAlgebra.Index B I) :
    scalarProjection (even (F := F) j) = MvPolynomial.X j := by simp [even]

theorem augmentation_derivative (i : I) (x : Odd F I) :
    ExteriorAlgebra.algebraMapInv (oddDerivative i x) = 0 := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap c => simp [oddDerivative]
  | ι v => simp [oddDerivative, ExteriorAlgebra.algebraMapInv, ExteriorAlgebra.lift_ι_apply]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul p q hp hq =>
    simp only [oddDerivative, ExteriorAlgebra.derivationOfLinear_mul, map_add, map_mul] at *
    rw [hp, hq, zero_mul, mul_zero, add_zero]

theorem scalarProjection_derivative (i : I) (p : A F B I) :
    scalarProjection (D i p) = ScalarJetAlgebra.totalDerivative i (scalarProjection p) := by
  induction p using TensorProduct.inductionOn with
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul x y =>
    simp only [D, totalDerivative_tmul, map_add, scalarProjection_tmul, augmentation_derivative]
    simp

theorem scalarProjection_word (w : List I) (p : A F B I) :
    scalarProjection (VariationalIBP.word D w p) =
      VariationalIBP.word (fun i => (ScalarJetAlgebra.totalDerivative i).toLinearMap) w (scalarProjection p) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [VariationalIBP.word, scalarProjection_derivative, ih]; rfl

def scalarCurrent : (I →₀ A F B I) →ₗ[ℂ] (I →₀ Scalar B I) :=
  Finsupp.mapRange.linearMap scalarProjection.toLinearMap

theorem scalarProjection_divergence (c : I →₀ A F B I) :
    scalarProjection (VariationalIBP.divergence D c) =
      DifferentialEquation.divergence (ScalarJetAlgebra.totalDerivative (S := B)) (scalarCurrent c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c e hc he => simp only [map_add, hc, he]
  | single i p =>
    simp [scalarCurrent, Finsupp.mapRange.linearMap_apply,
      scalarProjection_derivative, DifferentialEquation.divergence_single]

namespace Expr
def scalarEval (p : Expr Empty B I) : Scalar B I := scalarProjection p.eval
def scalarEuler (p : Expr Empty B I) (b : B) : Scalar B I := scalarProjection (p.euler (.inr b))
def scalarSeeds (p : Expr Empty B I) : Set (Scalar B I) := Set.range p.scalarEuler

@[simp] theorem scalarEval_add (p q : Expr Empty B I) :
    (p+q).scalarEval = p.scalarEval+q.scalarEval := map_add _ _ _

@[simp] theorem scalarEval_sub (p q : Expr Empty B I) :
    (p-q).scalarEval = p.scalarEval-q.scalarEval := by
  change scalarProjection (p.eval+(-q).eval) = scalarProjection p.eval-scalarProjection q.eval
  rw [eval_neg, map_add, map_neg, sub_eq_add_neg]

@[simp] theorem scalarEval_smul (c : ℂ) (p : Expr Empty B I) :
    (c • p).scalarEval = c • p.scalarEval := by
  simp only [scalarEval, eval_smul, map_smul]

@[simp] theorem scalarEval_pow (p : Expr Empty B I) (n : ℕ) :
    (p^n).scalarEval = p.scalarEval^n := by simp only [scalarEval, eval_pow, map_pow]

theorem scalarEval_derivative (i : I) (p : Expr Empty B I) :
    (derivative i p).scalarEval = ScalarJetAlgebra.totalDerivative i p.scalarEval := by
  exact (congrArg scalarProjection (eval_derivative i p)).trans (scalarProjection_derivative i p.eval)

def scalarInput {H : Type*} [Group H] (p : Expr Empty B I)
    (rho : Representation ℂ H (Scalar B I))
    (stable : ∀ h, DifferentialEquation.combined ScalarJetAlgebra.totalDerivative p.scalarSeeds ≤
      (DifferentialEquation.combined ScalarJetAlgebra.totalDerivative p.scalarSeeds).comap (rho h)) :=
  DerivativeInterface.equations ScalarJetAlgebra.totalDerivative p.scalarSeeds rho stable

def scalarTrivialInput (p : Expr Empty B I) :=
  p.scalarInput (Representation.trivial ℂ Unit _) (by intro h; exact le_refl _)

theorem scalar_input_relations {H : Type*} [Group H] (p : Expr Empty B I) (rho) (stable) :
    (p.scalarInput (H := H) rho stable).relations =
      TwoSidedDifferential.combined
        (fun i => (ScalarJetAlgebra.totalDerivative i).toLinearMap) p.scalarSeeds :=
  (TwoSidedDifferential.commutative_combined _ _).symm

theorem scalar_input_map {H : Type*} [Group H] (p : Expr Empty B I) (rho) (stable)
    (f : (p.scalarInput (H := H) rho stable).Coefficient) :
    (p.scalarInput rho stable).coefficientEquiv f =
      JetInputAdapter.equationEquiv ScalarJetAlgebra.totalDerivative p.scalarSeeds rho stable f := rfl

end Expr

def liftVariation (eta : B → Scalar B I) : Field Empty B → A Empty B I
  | .inl f => f.elim
  | .inr b => Algebra.TensorProduct.includeRight (eta b)

theorem liftVariation_parity (eta : B → Scalar B I) : PreservesParity (liftVariation eta) := by
  constructor
  · intro f; exact f.elim
  · intro b
    change MixedJetParity.involute ((1 : Odd Empty I) ⊗ₜ[ℂ] eta b) = _
    simp
    rfl

@[simp] theorem scalarProjection_liftVariation (eta : B → Scalar B I) (b : B) :
    scalarProjection (liftVariation eta (.inr b)) = eta b := by
  change scalarProjection ((1 : Odd Empty I) ⊗ₜ[ℂ] eta b) = _
  simp

theorem projected_bulk_mem (p : Expr Empty B I) (eta : B → Scalar B I) :
    scalarProjection (bulk (liftVariation eta) p.euler) ∈
      DifferentialEquation.ideal ScalarJetAlgebra.totalDerivative p.scalarSeeds := by
  rw [bulk, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  apply Ideal.sum_mem
  intro s hs
  cases s with
  | inl f => exact f.elim
  | inr b =>
    change scalarProjection (liftVariation eta (.inr b) * p.euler (.inr b)) ∈ _
    rw [map_mul, scalarProjection_liftVariation]
    exact Ideal.mul_mem_left _ _ (DifferentialEquation.seed_mem _ _ ⟨b, rfl⟩)

namespace Expr
theorem scalar_variation_agrees (p : Expr Empty B (Fin 4)) (eta : B → Scalar B (Fin 4)) :
    scalarProjection (p.variation (liftVariation eta)) = JetFirstVariation.variation eta p.scalarEval := by
  have hw (s : Field Empty B) (w : List (Fin 4)) :
      scalarProjection (VariationalIBP.word D w (liftVariation eta s)) =
        JetFirstVariation.variation eta (scalarProjection (jet s w : Expr Empty B (Fin 4)).eval) := by
    cases s with
    | inl f => exact f.elim
    | inr b =>
      rw [eval_jet_word]
      induction w with
      | nil => simp [VariationalIBP.word, eval, Expr.wordIndex]
      | cons i w ih =>
        simp only [VariationalIBP.word, scalarProjection_derivative,
          JetFirstVariation.variation_derivative, ih]
  induction p with
  | constant c => simp [variation, eval, scalarEval]
  | jet s w => exact hw s w
  | add p q hp hq => simpa only [variation, eval, scalarEval, map_add] using congrArg₂ (·+·) hp hq
  | mul p q hp hq =>
    simp only [variation, eval, scalarEval, map_add, map_mul, hp, hq,
      Derivation.leibniz, smul_eq_mul]
    ring

theorem scalar_first_variation (p : Expr Empty B (Fin 4)) (eta : B → Scalar B (Fin 4)) :
    JetFirstVariation.variation eta p.scalarEval =
      scalarProjection (bulk (liftVariation eta) p.euler) +
      DifferentialEquation.divergence ScalarJetAlgebra.totalDerivative
        (scalarCurrent (p.boundary (liftVariation eta))) := by
  rw [← scalar_variation_agrees, p.first_variation _ (liftVariation_parity eta),
    map_add, scalarProjection_divergence]

theorem scalar_onShell_variation (p : Expr Empty B (Fin 4)) (eta : B → Scalar B (Fin 4)) :
    p.scalarTrivialInput.projection (JetFirstVariation.variation eta p.scalarEval) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [scalar_first_variation]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (projected_bulk_mem p eta))
    (Submodule.mem_sup_right ⟨_, rfl⟩)

theorem scalar_substitution_first (p : Expr Empty B (Fin 4)) (eta : B → Scalar B (Fin 4)) :
    (JetFirstVariation.substitution eta p.scalarEval).coeff 1 =
      scalarProjection (p.variation (liftVariation eta)) := by
  rw [JetFirstVariation.substitution_first, scalar_variation_agrees]

theorem scalarEuler_add (p q : Expr Empty B I) (b : B) :
    (p+q).scalarEuler b = p.scalarEuler b + q.scalarEuler b := by
  simp only [scalarEuler, euler_add, Finsupp.add_apply, map_add]

theorem scalarEuler_smul (c : ℂ) (p : Expr Empty B I) (b : B) :
    (c • p).scalarEuler b = c • p.scalarEuler b := by
  simp only [scalarEuler, euler_smul, Finsupp.smul_apply, map_smul]

theorem scalarEuler_sub (p q : Expr Empty B I) (b : B) :
    (p-q).scalarEuler b = p.scalarEuler b-q.scalarEuler b := by
  simp only [scalarEuler, euler_sub, Finsupp.sub_apply, map_sub]

end Expr
end
end Math.LocalPolynomial
