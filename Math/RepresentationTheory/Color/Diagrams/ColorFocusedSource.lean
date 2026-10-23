import Math.RepresentationTheory.Color.Diagrams.ColorCertifiedTree

/-! Polarize every leaf except one chosen actual vertex. This promotes a
local trace exclusion to vanishing on the entire actual tensor source. -/
namespace Math.ColorFocusedSource
set_option autoImplicit false
noncomputable section
open Representation ColorTensorTree ColorFlagTree ColorCertifiedTree SU3DefiningExterior
open SplitRepresentationProjection
open scoped TensorProduct

def data : (t : Tree) → Leaf (shape t) → ColorTensorTree.Data
  | .leaf v, _ => { Carrier := v.Carrier, action := v.action }
  | .tensor l r, .inl i =>
    { Carrier := (data l i).Carrier ⊗[ℂ] ColorSymmetricTree.Carrier (shape r)
      action := (data l i).action.tprod (ColorSymmetricTree.action (shape r)) }
  | .tensor l r, .inr i =>
    { Carrier := ColorSymmetricTree.Carrier (shape l) ⊗[ℂ] (data r i).Carrier
      action := (ColorSymmetricTree.action (shape l)).tprod (data r i).action }

abbrev Carrier (t : Tree) (i : Leaf (shape t)) := (data t i).Carrier

def split : (t : Tree) → (i : Leaf (shape t)) →
    Split (ColorTensorTree.action (shape t)) (data t i).action
  | .leaf v, _ => v.split
  | .tensor l r, .inl i => (split l i).tensor (ColorSymmetricTree.split (shape r))
  | .tensor l r, .inr i => (ColorSymmetricTree.split (shape l)).tensor (split r i)

def fields : (t : Tree) → (i : Leaf (shape t)) →
    (Leaf (shape t) → Vector) → (Leaf (shape t) → Module.Dual ℂ Vector) →
    (vertexAt t i).Carrier → Carrier t i
  | .leaf _, _, _, _, x => x
  | .tensor l r, .inl i, v, f, x => fields l i (v ∘ Sum.inl) (f ∘ Sum.inl) x ⊗ₜ[ℂ]
      ColorSymmetricTree.pure (shape r) (v ∘ Sum.inr) (f ∘ Sum.inr)
  | .tensor l r, .inr i, v, f, x =>
    ColorSymmetricTree.pure (shape l) (v ∘ Sum.inl) (f ∘ Sum.inl) ⊗ₜ[ℂ]
      fields r i (v ∘ Sum.inr) (f ∘ Sum.inr) x

theorem ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    (t : Tree) (i : Leaf (shape t)) {F H : Carrier t i →ₗ[ℂ] N}
    (h : ∀ v f x, F (fields t i v f x) = H (fields t i v f x)) : F = H := by
  induction t generalizing N with
  | leaf v =>
    apply LinearMap.ext
    intro x
    exact h (fun _ => 0) (fun _ => 0) x
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      apply TensorProduct.ext'
      intro x y
      have hy : F.comp (TensorProduct.mk ℂ _ _ x) = H.comp (TensorProduct.mk ℂ _ _ x) := by
        apply ColorSymmetricTree.ext (shape r)
        intro v f
        have hx : F.comp ((TensorProduct.mk ℂ _ _).flip (ColorSymmetricTree.pure (shape r) v f)) =
            H.comp ((TensorProduct.mk ℂ _ _).flip (ColorSymmetricTree.pure (shape r) v f)) := by
          apply hl i
          intro u g z
          exact h (Sum.elim u v) (Sum.elim g f) z
        exact LinearMap.congr_fun hx x
      exact LinearMap.congr_fun hy y
    | inr i =>
      apply TensorProduct.ext'
      intro x y
      have hx : F.comp ((TensorProduct.mk ℂ _ _).flip y) = H.comp ((TensorProduct.mk ℂ _ _).flip y) := by
        apply ColorSymmetricTree.ext (shape l)
        intro v f
        have hy : F.comp (TensorProduct.mk ℂ _ _ (ColorSymmetricTree.pure (shape l) v f)) =
            H.comp (TensorProduct.mk ℂ _ _ (ColorSymmetricTree.pure (shape l) v f)) := by
          apply hr i
          intro u g z
          exact h (Sum.elim v u) (Sum.elim f g) z
        exact LinearMap.congr_fun hy y
      exact LinearMap.congr_fun hx x

def lift : (t : Tree) → (i : Leaf (shape t)) → ColorFlagTree.Carrier t →ₗ[ℂ] Carrier t i
  | .leaf _, _ => LinearMap.id
  | .tensor l r, .inl i => TensorProduct.map (lift l i) (symmetricMap r)
  | .tensor l r, .inr i => TensorProduct.map (symmetricMap l) (lift r i)

theorem lift_embed (t : Tree) (ht : Certified t) (i : Leaf (shape t)) (x : ColorFlagTree.Carrier t) :
    (split t i).embed (lift t i x) = (ColorFlagTree.split t).embed x := by
  induction t with
  | leaf v => rfl
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      induction x using TensorProduct.inductionOn with
      | tmul x y => exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) (hl ht.1 i x) (symmetricMap_embed r ht.2 y)
      | add x y hx hy =>
        exact (((split (.tensor l r) (Sum.inl i)).embed.toLinearMap.comp (lift (.tensor l r) (Sum.inl i))).map_add x y).trans
          ((congrArg₂ (·+·) hx hy).trans ((ColorFlagTree.split (.tensor l r)).embed.map_add x y).symm)
    | inr i =>
      induction x using TensorProduct.inductionOn with
      | tmul x y => exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) (symmetricMap_embed l ht.1 x) (hr ht.2 i y)
      | add x y hx hy =>
        exact (((split (.tensor l r) (Sum.inr i)).embed.toLinearMap.comp (lift (.tensor l r) (Sum.inr i))).map_add x y).trans
          ((congrArg₂ (·+·) hx hy).trans ((ColorFlagTree.split (.tensor l r)).embed.map_add x y).symm)

def rawVertex (t : Tree) (i : Leaf (shape t)) :
    (vertexAt t i).Carrier →ₗ[ℂ]
      SymmetricTensorTrace.Raw (V := Vector)
        (ColorTensorFocus.positiveAt (shape t) i) (ColorTensorFocus.negativeAt (shape t) i) :=
  (SymmetricVertexCertificate.cast rho (positiveAt t i).symm (negativeAt t i).symm).toLinearEquiv.toLinearMap.comp
    (vertexAt t i).split.embed.toLinearMap

theorem fields_embed (t : Tree) (i : Leaf (shape t))
    (v : Leaf (shape t) → Vector) (f : Leaf (shape t) → Module.Dual ℂ Vector) (x : (vertexAt t i).Carrier) :
    (split t i).embed (fields t i v f x) =
      ColorTensorFocus.focus (shape t) i v f (rawVertex t i x) := by
  induction t with
  | leaf a =>
    change a.split.embed x = SymmetricVertexCertificate.cast rho rfl rfl (a.split.embed x)
    exact (SymmetricVertexCertificate.cast_refl rho _ _ _).symm
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y)
        (hl i (v ∘ Sum.inl) (f ∘ Sum.inl) x)
        (ColorSymmetricTree.embed_pure (shape r) (v ∘ Sum.inr) (f ∘ Sum.inr))
    | inr i =>
      exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y)
        (ColorSymmetricTree.embed_pure (shape l) (v ∘ Sum.inl) (f ∘ Sum.inl))
        (hr i (v ∘ Sum.inr) (f ∘ Sum.inr) x)

theorem zero_of_local (t : Tree) (ht : Certified t) (i : Leaf (shape t))
    (F : ColorTensorTree.Carrier (shape t) →ₗ[ℂ] ℂ)
    (h : ∀ v f x, F (ColorTensorFocus.focus (shape t) i v f (rawVertex t i x)) = 0) :
    F.comp (ColorFlagTree.split t).embed.toLinearMap = 0 := by
  have hz : F.comp (split t i).embed.toLinearMap = 0 := by
    apply ext t i
    intro v f x
    change F ((split t i).embed (fields t i v f x)) = 0
    rw [fields_embed]
    exact h v f x
  apply LinearMap.ext
  intro x
  change F ((ColorFlagTree.split t).embed x) = 0
  rw [← lift_embed t ht i x]
  exact LinearMap.congr_fun hz (lift t i x)

end
end Math.ColorFocusedSource
