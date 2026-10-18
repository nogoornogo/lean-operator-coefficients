import Math.RepresentationTheory.SymmetricPowerDescent
import Math.RepresentationTheory.MixedWeightSupport

/-! Arbitrary exterior/symmetric mixed degrees, including zero degrees,
have inverse descent to alternating/symmetric multilinear maps. -/
namespace Math.MixedPowerDescent
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A B N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup N] [Module ℂ N]
  (n m : ℕ)

abbrev Domain := (⋀[ℂ]^n A) ⊗[ℂ] (Sym[ℂ]^m B)
abbrev Ordered := A [⋀^Fin n]→ₗ[ℂ] (SymmetricPowerDescent.symmetricMaps (A := B) (N := N) m)

def orderedEquiv : (Domain (A := A) (B := B) n m →ₗ[ℂ] N) ≃ₗ[ℂ]
    Ordered (A := A) (B := B) (N := N) n m :=
  (TensorProduct.lift.equiv (RingHom.id ℂ) (⋀[ℂ]^n A) (Sym[ℂ]^m B) N).symm.trans
    ((LinearEquiv.arrowCongr (LinearEquiv.refl ℂ (⋀[ℂ]^n A))
      (SymmetricPowerDescent.equiv m)).trans exteriorPower.alternatingMapLinearEquiv.symm)

@[simp] theorem orderedEquiv_apply (f : Domain (A := A) (B := B) n m →ₗ[ℂ] N)
    (v : Fin n → A) (w : Fin m → B) :
    (orderedEquiv n m f v).val w = f (MixedWeightSupport.pure v w) := rfl

@[simp] theorem lift_apply (f : Ordered (A := A) (B := B) (N := N) n m)
    (v : Fin n → A) (w : Fin m → B) :
    (orderedEquiv n m).symm f (MixedWeightSupport.pure v w) = (f v).val w := by
  simpa only [orderedEquiv_apply] using congrArg
    (fun k : Ordered (A := A) (B := B) (N := N) n m => (k v).val w)
    ((orderedEquiv n m).apply_symm_apply f)

theorem ext {f g : Domain (A := A) (B := B) n m →ₗ[ℂ] N}
    (h : ∀ v w, f (MixedWeightSupport.pure v w) = g (MixedWeightSupport.pure v w)) : f = g := by
  apply (orderedEquiv n m).injective
  apply AlternatingMap.ext
  intro v
  apply Subtype.ext
  apply MultilinearMap.ext
  exact h v

section Equivariant
variable {G : Type*} [Group G]
  (a : Representation ℂ G A) (b : Representation ℂ G B) (t : Representation ℂ G N)

def equivariantOrdered : Submodule ℂ (Ordered (A := A) (B := B) (N := N) n m) where
  carrier := {f | ∀ g v w, (f (a g ∘ v)).val (b g ∘ w) = t g ((f v).val w)}
  zero_mem' := by intro g v w; exact (map_zero (t g)).symm
  add_mem' := by
    intro f q hf hq g v w
    change (f _).val _ + (q _).val _ = t g ((f v).val w + (q v).val w)
    rw [hf, hq, map_add]
  smul_mem' := by
    intro z f hf g v w
    change z • (f _).val _ = t g (z • (f v).val w)
    rw [hf, map_smul]

def descend (f : equivariantOrdered n m a b t) :
    Representation.IntertwiningMap ((a.exteriorPower n).tprod (b.symmetricPower m)) t where
  toLinearMap := (orderedEquiv n m).symm f.val
  isIntertwining' g := by
    apply ext n m
    intro v w
    change (orderedEquiv n m).symm f.val
      ((a.exteriorPower n) g (exteriorPower.ιMulti ℂ n v) ⊗ₜ[ℂ]
        (b.symmetricPower m) g (SymmetricPower.tprod ℂ w)) =
      t g ((orderedEquiv n m).symm f.val (MixedWeightSupport.pure v w))
    rw [Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod]
    change (orderedEquiv n m).symm f.val (MixedWeightSupport.pure (a g ∘ v) (b g ∘ w)) =
      t g ((orderedEquiv n m).symm f.val (MixedWeightSupport.pure v w))
    rw [lift_apply, lift_apply]
    exact f.property g v w

def equivariantEquiv :
    Representation.IntertwiningMap ((a.exteriorPower n).tprod (b.symmetricPower m)) t ≃ₗ[ℂ]
      equivariantOrdered n m a b t where
  toFun f := ⟨orderedEquiv n m f.toLinearMap, by
    intro g v w
    simp only [orderedEquiv_apply]
    change f (MixedWeightSupport.pure (a g ∘ v) (b g ∘ w)) =
      t g (f (MixedWeightSupport.pure v w))
    have he := Representation.IntertwiningMap.isIntertwining _ _ f g
      (MixedWeightSupport.pure v w)
    simpa only [MixedWeightSupport.pure, Representation.tprod_apply, TensorProduct.map_tmul,
      Representation.exteriorPower_apply_ιMulti,
      Representation.symmetricPower_apply_tprod, Function.comp_def] using he⟩
  invFun := descend n m a b t
  left_inv f := by
    apply Representation.IntertwiningMap.ext
    exact (orderedEquiv n m).symm_apply_apply f.toLinearMap
  right_inv f := by apply Subtype.ext; exact (orderedEquiv n m).apply_symm_apply f.val
  map_add' f q := by apply Subtype.ext; exact (orderedEquiv n m).map_add _ _
  map_smul' z f := by apply Subtype.ext; exact (orderedEquiv n m).map_smul z _

end Equivariant
end
end Math.MixedPowerDescent
