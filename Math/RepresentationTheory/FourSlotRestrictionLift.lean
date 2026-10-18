import Math.RepresentationTheory.FourSlotSpeciesRestriction
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! Restriction and reconstruction for degree-(2,1,1) exterior coefficients. -/
namespace Math.FourSlotRestrictionLift
set_option autoImplicit false
noncomputable section
open Representation FourSlotAlternation FourSlotSpeciesDegree FourSlotSpeciesRestriction
open scoped TensorProduct

section Curry
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private def evalEmpty : MultilinearMap ℂ (fun _ : Fin 0 => V) ℂ →ₗ[ℂ] ℂ where
  toFun f := f Fin.elim0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def curryOne : MultilinearMap ℂ (fun _ : Fin 1 => V) ℂ →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ evalEmpty).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 1 => V) ℂ).toLinearMap

private def curryTwo : MultilinearMap ℂ (fun _ : Fin 2 => V) ℂ →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryOne).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 2 => V) ℂ).toLinearMap

private def curryThree : MultilinearMap ℂ (fun _ : Fin 3 => V) ℂ →ₗ[ℂ]
    V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryTwo).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 3 => V) ℂ).toLinearMap

private def curryFour : MultilinearMap ℂ (fun _ : Fin 4 => V) ℂ →ₗ[ℂ]
    V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] V →ₗ[ℂ] ℂ :=
  (LinearMap.llcomp ℂ V _ _ curryThree).comp
    (multilinearCurryLeftEquiv ℂ (fun _ : Fin 4 => V) ℂ).toLinearMap
end Curry

variable {H A B C : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

private def lastPair :
    (Fields A B C →ₗ[ℂ] Fields A B C →ₗ[ℂ] ℂ) →ₗ[ℂ] (B ⊗[ℂ] C) →ₗ[ℂ] ℂ where
  toFun f := TensorProduct.lift (f.compl₁₂
    ((LinearMap.inr ℂ A (B × C)).comp (LinearMap.inl ℂ B C))
    ((LinearMap.inr ℂ A (B × C)).comp (LinearMap.inr ℂ B C)))
  map_add' f g := by ext x y; rfl
  map_smul' z f := by ext x y; rfl

variable (a : Representation ℂ H A) (b : Representation ℂ H B) (c : Representation ℂ H C)

def linearRestriction (f : coefficients a b c) :
    ((A ⊗[ℂ] A) ⊗[ℂ] (B ⊗[ℂ] C)) →ₗ[ℂ] ℂ :=
  TensorProduct.lift (lastPair.comp (TensorProduct.lift
    ((curryFour (evaluation a b c f).toMultilinearMap).compl₁₂
      (LinearMap.inl ℂ A (B × C)) (LinearMap.inl ℂ A (B × C)))))

theorem linearRestriction_apply (f : coefficients a b c) (x y : A) (u : B) (e : C) :
    linearRestriction a b c f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) =
      f (exteriorPower.ιMulti ℂ 4 (slots x y u e)) := rfl

def restriction (f : coefficients a b c) :
    IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ) where
  toLinearMap := linearRestriction a b c f
  isIntertwining' h := by
    ext x y u e
    change f (exteriorPower.ιMulti ℂ 4 (slots (a h x) (a h y) (b h u) (c h e))) =
      f (exteriorPower.ιMulti ℂ 4 (slots x y u e))
    have hi := IntertwiningMap.isIntertwining _ _ f h
      (exteriorPower.ιMulti ℂ 4 (slots x y u e))
    rw [Representation.exteriorPower_apply_ιMulti] at hi
    have hv : (fun i => action a b c h (slots x y u e i)) =
        slots (a h x) (a h y) (b h u) (c h e) := by
      funext i
      fin_cases i <;> simp [slots, action]
    change f (exteriorPower.ιMulti ℂ 4 (fun i => action a b c h (slots x y u e i))) = _ at hi
    rw [hv] at hi
    exact hi

theorem restriction_swap (f : coefficients a b c) (x y : A) (u : B) (e : C) :
    f (exteriorPower.ιMulti ℂ 4 (slots y x u e)) =
      -f (exteriorPower.ιMulti ℂ 4 (slots x y u e)) := by
  have he := (evaluation a b c f).map_swap (slots x y u e) (by decide : (0 : Fin 4) ≠ 1)
  have hv : slots x y u e ∘ Equiv.swap 0 1 = slots y x u e := by
    funext i
    fin_cases i <;> norm_num [slots, Equiv.swap_apply_def, Function.comp_def]
  rw [hv] at he
  exact he

theorem reconstruct (f : coefficients a b c) (hf : HasDegree a b c f) :
    coefficient a b c ((1 / 2 : ℂ) • restriction a b c f) = f := by
  apply slots_ext a b c _ f (coefficient_hasDegree a b c _) hf
  intro x y u e
  rw [coefficient_slots]
  change (1 / 2 : ℂ) * f (exteriorPower.ιMulti ℂ 4 (slots x y u e)) -
    (1 / 2 : ℂ) * f (exteriorPower.ιMulti ℂ 4 (slots y x u e)) = _
  rw [restriction_swap]
  ring

theorem exists_ordered (f : coefficients a b c) (hf : HasDegree a b c f) :
    ∃ g : IntertwiningMap ((a.tprod a).tprod (b.tprod c)) (Representation.trivial ℂ H ℂ),
      coefficient a b c g = f :=
  ⟨(1 / 2 : ℂ) • restriction a b c f, reconstruct a b c f hf⟩

end
end Math.FourSlotRestrictionLift
