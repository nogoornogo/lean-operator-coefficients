import Math.RepresentationTheory.MixedPowerDescent
import Math.RepresentationTheory.LocalExchangeHom

namespace Math.MixedPowerRegression
noncomputable section
open scoped TensorProduct
variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

theorem two_boson_inverse
    (f : MixedPowerDescent.Domain (A := A) (B := B) 2 2 →ₗ[ℂ] ℂ) :
    (MixedPowerDescent.orderedEquiv 2 2).symm (MixedPowerDescent.orderedEquiv 2 2 f) = f :=
  (MixedPowerDescent.orderedEquiv 2 2).symm_apply_apply f

theorem boson_exchange
    (f : MixedPowerDescent.Domain (A := A) (B := B) 2 2 →ₗ[ℂ] ℂ)
    (v : Fin 2 → A) (w : Fin 2 → B) (p : Equiv.Perm (Fin 2)) :
    f (MixedWeightSupport.pure v (w ∘ p)) = f (MixedWeightSupport.pure v w) :=
  (MixedPowerDescent.orderedEquiv 2 2 f v).property p w

theorem repeated_fermion_vanish
    (f : MixedPowerDescent.Domain (A := A) (B := B) 2 2 →ₗ[ℂ] ℂ)
    (v : Fin 2 → A) (w : Fin 2 → B) (h : v 0 = v 1) :
    f (MixedWeightSupport.pure v w) = 0 := by
  have hz := (MixedPowerDescent.orderedEquiv 2 2 f).map_eq_zero_of_eq v h (by decide : (0 : Fin 2) ≠ 1)
  have he := congrArg (fun q : SymmetricPowerDescent.symmetricMaps (A := B) (N := ℂ) 2 => q.val w) hz
  exact he
end
end Math.MixedPowerRegression

open Lean in
run_cmd do
  let ds := [
    ``Math.SymmetricPowerDescent.lift,
    ``Math.SymmetricPowerDescent.equiv,
    ``Math.SymmetricPowerDescent.lift_tprod,
    ``Math.MixedPowerDescent.orderedEquiv,
    ``Math.MixedPowerDescent.lift_apply,
    ``Math.MixedPowerDescent.ext,
    ``Math.MixedPowerDescent.equivariantEquiv,
    ``Math.LocalExchangeHom.transport,
    ``Math.LocalExchangeHom.equiv,
    ``Math.LocalExchangeHom.equiv_mk,
    ``Math.MixedPowerRegression.two_boson_inverse,
    ``Math.MixedPowerRegression.boson_exchange,
    ``Math.MixedPowerRegression.repeated_fermion_vanish]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed power descent {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed power descent: {ds.length} strict transitive checks passed"
