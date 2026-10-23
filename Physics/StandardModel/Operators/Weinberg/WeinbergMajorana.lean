import Physics.StandardModel.Operators.Weinberg.WeinbergResidualHom
import Physics.FieldTheory.Mass.Algebra.InvariantMassData

open Math

/-! Specified-VEV evaluation of regrouped Weinberg coefficients.
Only the residual group acts on the resulting flavor mass. No vacuum selection
or nonzero matching coefficient is inferred. -/
namespace Physics.WeinbergMajorana
set_option autoImplicit false
noncomputable section
open Representation SMEpsilonTensor WeinbergResidualHom
open scoped TensorProduct

variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

abbrev MassCoefficients := TensorSquareMultilinear.symmetricIntertwiners a
  (Representation.trivial ℂ R ℂ)

def evaluate (v : ℂ) : sector a →ₗ[ℂ] MassCoefficients a :=
  v ^ 2 • (symmetricEquiv a).toLinearMap

def mass (v : ℂ) (f : sector a) : InvariantWeylMass.SymmetricMass a where
  form := TensorProduct.curry (evaluate a v f).val.toLinearMap
  symmetric := ⟨fun u w => ((evaluate a v f).property u w).symm⟩
  invariant r u w := IntertwiningMap.isIntertwining _ _ (evaluate a v f).val r (u ⊗ₜ[ℂ] w)

/-- The standard neutral Higgs direction; this is supplied, not dynamically derived. -/
def vacuum (v : ℂ) : Weak := v • weakBasis 1

theorem evaluation_formula (v : ℂ) (f : sector a) (u w : F) :
    f.val (input (weakBasis 0) (weakBasis 0) ![vacuum v,vacuum v]
      (weakBasis 0) (weakBasis 1) u w) = (mass a v f).form u w := by
  rw [reconstruction, WeinbergWeakInvariant.diagonal_apply]
  change eps2 (weakBasis 0) (vacuum v) * eps2 (weakBasis 0) (vacuum v) *
    eps2 (weakBasis 0) (weakBasis 1) * factorEquiv a f.val (u ⊗ₜ[ℂ] w) =
      v ^ 2 * factorEquiv a f.val (u ⊗ₜ[ℂ] w)
  simp [vacuum, pow_two]

def evaluationEquiv (v : ℂ) (hv : v ≠ 0) : sector a ≃ₗ[ℂ] MassCoefficients a :=
  (symmetricEquiv a).trans (LinearEquiv.smulOfNeZero ℂ (MassCoefficients a)
    (v ^ 2) (pow_ne_zero _ hv))

@[simp] theorem evaluationEquiv_apply (v : ℂ) (hv : v ≠ 0) (f : sector a) :
    evaluationEquiv a v hv f = evaluate a v f := rfl

theorem evaluate_nonzero_iff (v : ℂ) (hv : v ≠ 0) (f : sector a) :
    evaluate a v f ≠ 0 ↔ f ≠ 0 :=
  not_congr (evaluationEquiv a v hv).map_eq_zero_iff

@[simp] theorem evaluate_zero (f : sector a) : evaluate a 0 f = 0 := by
  simp [evaluate]

end
end Physics.WeinbergMajorana
