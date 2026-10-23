import Math.RepresentationTheory.Constructions.FiniteGroupPolynomialEvaluation
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Finite-group polynomial evaluation into residual invariant functionals. -/
namespace Math.PolynomialCovariantEvaluation
noncomputable section
open Representation
variable {H I J V : Type*} [Group H]
  [AddCommGroup V] [Module ℂ V]

/-- Coordinate transport of a representation, without any change of action. -/
def coordinateAction (e : V ≃ₗ[ℂ] (J → ℂ)) (r : Representation ℂ H V) :
    Representation ℂ H (J → ℂ) where
  toFun g := e.toLinearMap.comp ((r g).comp e.symm.toLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul, Module.End.mul_apply]

@[simp] theorem coordinateAction_apply (e : V ≃ₗ[ℂ] (J → ℂ))
    (r : Representation ℂ H V) (g : H) (x : J → ℂ) :
    coordinateAction e r g x = e (r g (e.symm x)) := rfl

/-- Source-coordinate transport preserves the actual stabilizer, at every value. -/
@[simp] theorem coordinate_stabilizer (e : V ≃ₗ[ℂ] (J → ℂ))
    (r : Representation ℂ H V) (s : V) (g : H) :
    g ∈ stabilizer (coordinateAction e r) (e s) ↔ r g s = s := by
  change e (r g (e.symm (e s))) = e s ↔ _
  simp

/-- The fixed dual space, in supplied coordinates, is exactly residual Hom.
The dual convention is `(g f)(q) = f(g⁻¹ q)`. -/
def fixedDualEquiv (r : Representation ℂ H V)
    (e : Module.Dual ℂ V ≃ₗ[ℂ] (J → ℂ)) (K : Subgroup H) :
    (Representation.invariants ((coordinateAction e r.dual).comp K.subtype)) ≃ₗ[ℂ]
      IntertwiningMap (r.comp K.subtype) (trivial ℂ K ℂ) where
  toFun w := {
    toLinearMap := e.symm w.val
    isIntertwining' g := by
      ext q
      have hw := w.property g⁻¹
      change e (r.dual (g.val⁻¹) (e.symm w.val)) = w.val at hw
      have hf := congrArg e.symm hw
      have hq := congrArg (fun f : Module.Dual ℂ V => f q) hf
      simpa [Representation.dual, Representation.trivial] using hq }
  invFun f := ⟨e f.toLinearMap, by
    intro g
    change e (r.dual g.val (e.symm (e f.toLinearMap))) = e f.toLinearMap
    simp only [e.symm_apply_apply]
    apply congrArg e
    ext q
    exact congrArg (fun L : V →ₗ[ℂ] ℂ => L q) (f.isIntertwining' (g⁻¹))⟩
  left_inv w := by apply Subtype.ext; exact e.apply_symm_apply w.val
  right_inv f := by
    ext q
    exact congrArg (fun l : Module.Dual ℂ V => l q) (e.symm_apply_apply f.toLinearMap)
  map_add' u v := by
    ext q
    exact congrArg (fun l : Module.Dual ℂ V => l q) (e.symm.map_add u.val v.val)
  map_smul' z u := by
    ext q
    exact congrArg (fun l : Module.Dual ℂ V => l q) (e.symm.map_smul z u.val)

variable [Fintype H] [Fintype I] [Fintype J]
  (a : Representation ℂ H (I → ℂ)) (r : Representation ℂ H V)
  (e : Module.Dual ℂ V ≃ₗ[ℂ] (J → ℂ))

/-- Evaluate a polynomial dual covariant as a residual invariant coefficient. -/
def coefficientEvaluation (s : I → ℂ) :
    covariants a (coordinateAction e r.dual) →ₗ[ℂ]
      IntertwiningMap (r.comp (stabilizer a s).subtype)
        (trivial ℂ (stabilizer a s) ℂ) :=
  (fixedDualEquiv r e (stabilizer a s)).toLinearMap.comp
    (evaluation a (coordinateAction e r.dual) s)

/-- Every residual invariant coefficient is obtained from a polynomial spurion
covariant. Coordinates are supplied only on the finite-dimensional dual. -/
theorem coefficientEvaluation_surjective (s : I → ℂ) :
    Function.Surjective (coefficientEvaluation a r e s) :=
  (fixedDualEquiv r e (stabilizer a s)).surjective.comp
    (finite_group_surjective a (coordinateAction e r.dual) s)
/-- Choosing a basis supplies the dual-coordinate input for every finite-dimensional
residual quotient. No basis is an extra mathematical hypothesis. -/
theorem finite_dimensional_coefficients [FiniteDimensional ℂ V] (s : I → ℂ) :
    Function.Surjective (coefficientEvaluation a r
      (Module.finBasis ℂ (Module.Dual ℂ V)).equivFun s) :=
  coefficientEvaluation_surjective a r _ s

/-- Nonzero residual coefficients exist exactly when some polynomial evaluation
is nonzero. This is an existence statement, not UV matching. -/
theorem nonzero_coefficient_iff (s : I → ℂ) :
    (∃ f : IntertwiningMap (r.comp (stabilizer a s).subtype)
      (trivial ℂ (stabilizer a s) ℂ), f ≠ 0) ↔
    ∃ p, coefficientEvaluation a r e s p ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨p, hp⟩ := coefficientEvaluation_surjective a r e s f
    exact ⟨p, hp ▸ hf⟩
  · rintro ⟨p, hp⟩
    exact ⟨_, hp⟩
end
end Math.PolynomialCovariantEvaluation
