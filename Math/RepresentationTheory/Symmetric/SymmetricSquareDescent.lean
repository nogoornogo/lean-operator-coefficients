import TauCeti.RepresentationTheory.SymmetricPower
import Mathlib.Tactic

/-! The universal property needed for qque's repeated species.
This uses the independently defined symmetric-power quotient, not an image. -/

namespace Math.SymmetricSquareDescent
noncomputable section
open scoped TensorProduct

variable {A N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup N] [Module ℂ N]

def IsSymmetric (f : MultilinearMap ℂ (fun _ : Fin 2 => A) N) : Prop :=
  ∀ (e : Equiv.Perm (Fin 2)) (v : Fin 2 → A), f (v ∘ e) = f v

def lift (f : MultilinearMap ℂ (fun _ : Fin 2 => A) N)
    (hf : IsSymmetric f) : Sym[ℂ]^2 A →ₗ[ℂ] N where
  toFun := (addConGen (SymmetricPower.Rel ℂ (Fin 2) A)).lift
    (PiTensorProduct.lift f).toAddMonoidHom (by
      apply AddCon.addConGen_le.2
      intro x y h
      cases h with
      | perm e v =>
        apply (AddCon.ker_rel _).2
        simp only [LinearMap.toAddMonoidHom_coe, PiTensorProduct.lift.tprod]
        exact (hf e v).symm)
  map_add' := map_add _
  map_smul' z x := AddCon.induction_on x fun x => (PiTensorProduct.lift f).map_smul z x

@[simp] theorem lift_tprod (f : MultilinearMap ℂ (fun _ : Fin 2 => A) N)
    (hf : IsSymmetric f) (v : Fin 2 → A) :
    lift f hf (SymmetricPower.tprod ℂ v) = f v := by
  change PiTensorProduct.lift f (PiTensorProduct.tprod ℂ v) = f v
  simp

theorem ext {f g : Sym[ℂ]^2 A →ₗ[ℂ] N}
    (h : ∀ v, f (SymmetricPower.tprod ℂ v) = g (SymmetricPower.tprod ℂ v)) : f = g := by
  apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin 2) A)
  rintro _ ⟨v, rfl⟩
  exact h v

abbrev symmetricMaps : Submodule ℂ (MultilinearMap ℂ (fun _ : Fin 2 => A) N) where
  carrier := {f | IsSymmetric f}
  zero_mem' := by intro e v; rfl
  add_mem' := by
    intro f g hf hg e v
    change f (v ∘ e) + g (v ∘ e) = f v + g v
    rw [hf e v, hg e v]
  smul_mem' := by
    intro z f hf e v
    change z • f (v ∘ e) = z • f v
    rw [hf e v]

def equiv : (Sym[ℂ]^2 A →ₗ[ℂ] N) ≃ₗ[ℂ] (symmetricMaps (A := A) (N := N)) where
  toFun f := ⟨f.compMultilinearMap (SymmetricPower.tprod ℂ), by
    intro e v
    change f (SymmetricPower.tprod ℂ (fun i => v (e i))) = f (SymmetricPower.tprod ℂ v)
    rw [SymmetricPower.tprod_equiv]⟩
  invFun f := lift f f.property
  left_inv f := by
    apply ext
    intro v
    exact lift_tprod _ _ v
  right_inv f := by
    apply Subtype.ext
    ext v
    exact lift_tprod (A := A) (N := N) f.val f.property v
  map_add' f g := by
    apply Subtype.ext
    ext v
    rfl
  map_smul' z f := by
    apply Subtype.ext
    ext v
    rfl

section Equivariant
variable {H : Type*} [Group H]
  (a : Representation ℂ H A) (n : Representation ℂ H N)

abbrev equivariantMaps : Submodule ℂ (symmetricMaps (A := A) (N := N)) where
  carrier := {f | ∀ h v, f.val (fun i => a h (v i)) = n h (f.val v)}
  zero_mem' := by intro h v; exact (map_zero (n h)).symm
  add_mem' := by
    intro f g hf hg h v
    change f.val _ + g.val _ = n h (f.val v + g.val v)
    rw [hf h v, hg h v, map_add]
  smul_mem' := by
    intro z f hf h v
    change z • f.val _ = n h (z • f.val v)
    rw [hf h v, map_smul]

def descend (f : equivariantMaps a n) :
    Representation.IntertwiningMap (a.symmetricPower 2) n where
  toLinearMap := lift f.val.val f.val.property
  isIntertwining' h := by
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin 2) A)
    rintro _ ⟨v, rfl⟩
    change lift f.val.val f.val.property ((a.symmetricPower 2) h (SymmetricPower.tprod ℂ v)) =
      n h (lift f.val.val f.val.property (SymmetricPower.tprod ℂ v))
    rw [Representation.symmetricPower_apply_tprod, lift_tprod, lift_tprod]
    exact f.property h v

def equivariantEquiv : Representation.IntertwiningMap (a.symmetricPower 2) n ≃ₗ[ℂ]
    equivariantMaps a n where
  toFun f := ⟨equiv f.toLinearMap, by
    intro h v
    change f (SymmetricPower.tprod ℂ (fun i => a h (v i))) =
      n h (f (SymmetricPower.tprod ℂ v))
    rw [← Representation.symmetricPower_apply_tprod]
    exact Representation.IntertwiningMap.isIntertwining _ _ f h _⟩
  invFun := descend a n
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    exact equiv.left_inv f.toLinearMap
  right_inv f := by
    apply Subtype.ext
    exact equiv.right_inv f.val
  map_add' f g := by
    apply Subtype.ext
    exact equiv.map_add f.toLinearMap g.toLinearMap
  map_smul' z f := by
    apply Subtype.ext
    exact equiv.map_smul z f.toLinearMap

end Equivariant

end
end Math.SymmetricSquareDescent
