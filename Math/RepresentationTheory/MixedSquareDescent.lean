import Math.RepresentationTheory.SymmetricSquareDescent
import TauCeti.RepresentationTheory.ExteriorPower

/-! Mixed statistics: an alternating fermion pair and a symmetric boson pair.
The source is the independent exterior/symmetric tensor product, not an image. -/
namespace Math.MixedSquareDescent
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

variable {A B N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup N] [Module ℂ N]

abbrev Domain (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] := (⋀[ℂ]^2 A) ⊗[ℂ] (Sym[ℂ]^2 B)

abbrev Ordered := A [⋀^Fin 2]→ₗ[ℂ] (SymmetricSquareDescent.symmetricMaps (A := B) (N := N))

/-- Composing three universal properties gives both directions without choosing bases. -/
def orderedEquiv : (Domain A B →ₗ[ℂ] N) ≃ₗ[ℂ] Ordered (A := A) (B := B) (N := N) :=
  (TensorProduct.lift.equiv (RingHom.id ℂ) (⋀[ℂ]^2 A) (Sym[ℂ]^2 B) N).symm.trans
    ((LinearEquiv.arrowCongr (LinearEquiv.refl ℂ (⋀[ℂ]^2 A))
      SymmetricSquareDescent.equiv).trans exteriorPower.alternatingMapLinearEquiv.symm)

@[simp] theorem orderedEquiv_apply (f : Domain A B →ₗ[ℂ] N)
    (a : Fin 2 → A) (b : Fin 2 → B) :
    (orderedEquiv f a).val b =
      f (exteriorPower.ιMulti ℂ 2 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ b) := rfl

@[simp] theorem lift_apply (f : Ordered (A := A) (B := B) (N := N))
    (a : Fin 2 → A) (b : Fin 2 → B) :
    orderedEquiv.symm f
      (exteriorPower.ιMulti ℂ 2 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ b) = (f a).val b := by
  simpa only [orderedEquiv_apply] using
    congrArg (fun k : Ordered (A := A) (B := B) (N := N) => (k a).val b)
      (orderedEquiv.apply_symm_apply f)

theorem ext {f g : Domain A B →ₗ[ℂ] N}
    (h : ∀ a b, f (exteriorPower.ιMulti ℂ 2 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ b) =
      g (exteriorPower.ιMulti ℂ 2 a ⊗ₜ[ℂ] SymmetricPower.tprod ℂ b)) : f = g := by
  apply orderedEquiv.injective
  apply AlternatingMap.ext
  intro a
  apply Subtype.ext
  apply MultilinearMap.ext
  exact h a

section Equivariant
variable {R : Type*} [Group R]
  (a : Representation ℂ R A) (b : Representation ℂ R B) (n : Representation ℂ R N)

def representation : Representation ℂ R (Domain A B) :=
  (a.exteriorPower 2).tprod (b.symmetricPower 2)

def equivariantOrdered : Submodule ℂ (Ordered (A := A) (B := B) (N := N)) where
  carrier := {f | ∀ r x y, (f (a r ∘ x)).val (b r ∘ y) = n r ((f x).val y)}
  zero_mem' := by intro r x y; exact (map_zero (n r)).symm
  add_mem' := by
    intro f g hf hg r x y
    change (f _).val _ + (g _).val _ = n r ((f x).val y + (g x).val y)
    rw [hf, hg, map_add]
  smul_mem' := by
    intro z f hf r x y
    change z • (f _).val _ = n r (z • (f x).val y)
    rw [hf, map_smul]

def descend (f : equivariantOrdered a b n) :
    Representation.IntertwiningMap (representation a b) n where
  toLinearMap := orderedEquiv.symm f.val
  isIntertwining' r := by
    apply ext
    intro x y
    change orderedEquiv.symm f.val
      ((a.exteriorPower 2) r (exteriorPower.ιMulti ℂ 2 x) ⊗ₜ[ℂ]
        (b.symmetricPower 2) r (SymmetricPower.tprod ℂ y)) =
      n r (orderedEquiv.symm f.val
        (exteriorPower.ιMulti ℂ 2 x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ y))
    rw [Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod, lift_apply, lift_apply]
    exact f.property r x y

/-- Equivariance is checked on pure mixed generators, with no dimension assumptions. -/
def equivariantEquiv :
    Representation.IntertwiningMap (representation a b) n ≃ₗ[ℂ]
      equivariantOrdered a b n where
  toFun f := ⟨orderedEquiv f.toLinearMap, by
    intro r x y
    simp only [orderedEquiv_apply]
    change f (exteriorPower.ιMulti ℂ 2 (a r ∘ x) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (b r ∘ y)) =
      n r (f (exteriorPower.ιMulti ℂ 2 x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ y))
    have h := Representation.IntertwiningMap.isIntertwining _ _ f r
      (exteriorPower.ιMulti ℂ 2 x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ y)
    simpa only [representation, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod, Function.comp_def] using h⟩
  invFun := descend a b n
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    exact orderedEquiv.symm_apply_apply f.toLinearMap
  right_inv f := by
    apply Subtype.ext
    exact orderedEquiv.apply_symm_apply f.val
  map_add' f g := by
    apply Subtype.ext
    exact orderedEquiv.map_add f.toLinearMap g.toLinearMap
  map_smul' z f := by
    apply Subtype.ext
    exact orderedEquiv.map_smul z f.toLinearMap

end Equivariant

end
end Math.MixedSquareDescent
