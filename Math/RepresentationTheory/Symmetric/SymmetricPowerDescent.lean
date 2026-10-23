import TauCeti.RepresentationTheory.SymmetricPower
import TauCeti.LinearAlgebra.SymmetricPower.Lift
import Mathlib.Basic.Complex.Basic

/-! Basis-free inverse descent for arbitrary symmetric tensor degree. -/
namespace Math.SymmetricPowerDescent
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup N] [Module ℂ N] (m : ℕ)

def symmetricMaps : Submodule ℂ (MultilinearMap ℂ (fun _ : Fin m => A) N) where
  carrier := {f | ∀ (e : Equiv.Perm (Fin m)) v, f (v ∘ e) = f v}
  zero_mem' := by intro e v; rfl
  add_mem' := by
    intro f g hf hg e v
    change f (v ∘ e) + g (v ∘ e) = f v + g v
    rw [hf, hg]
  smul_mem' := by
    intro z f hf e v
    change z • f (v ∘ e) = z • f v
    rw [hf]

def lift (f : symmetricMaps (A := A) (N := N) m) : Sym[ℂ]^m A →ₗ[ℂ] N :=
  SymmetricPower.lift f.val (by
    intro e
    ext v
    exact f.property e v)

@[simp] theorem lift_tprod (f : symmetricMaps (A := A) (N := N) m) (v : Fin m → A) :
    lift m f (SymmetricPower.tprod ℂ v) = f.val v := SymmetricPower.lift_tprod _ _ _

def equiv : (Sym[ℂ]^m A →ₗ[ℂ] N) ≃ₗ[ℂ] symmetricMaps (A := A) (N := N) m where
  toFun f := ⟨f.compMultilinearMap (SymmetricPower.tprod ℂ), by
    intro e v
    change f (SymmetricPower.tprod ℂ (fun i => v (e i))) = f (SymmetricPower.tprod ℂ v)
    rw [SymmetricPower.tprod_equiv]⟩
  invFun := lift m
  left_inv f := by
    apply SymmetricPower.ext
    intro v
    exact lift_tprod _ _ _
  right_inv f := by
    apply Subtype.ext
    ext v
    exact lift_tprod _ _ _
  map_add' f g := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

end
end Math.SymmetricPowerDescent
