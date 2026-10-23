import Math.RepresentationTheory.Color.Diagrams.ColorFlagTree
import Math.RepresentationTheory.Color.Diagrams.ColorVertexCertificates
import Math.RepresentationTheory.Color.Diagrams.ColorTensorFocus

/-! Certified actual color trees factor through the full symmetric source.
Repeated determinant owners therefore vanish on every actual source vector. -/
namespace Math.ColorCertifiedTree
set_option autoImplicit false
noncomputable section
open Representation ColorFlagTree SU3DefiningExterior
open scoped TensorProduct

def Certified : Tree → Prop
  | .leaf v => ColorVertexCertificates.Certified v
  | .tensor l r => Certified l ∧ Certified r

def vertexAt : (t : Tree) → ColorTensorTree.Leaf (shape t) → ColorFlagVertex.Vertex
  | .leaf v, _ => v
  | .tensor l _r, .inl i => vertexAt l i
  | .tensor _l r, .inr i => vertexAt r i

theorem positiveAt (t : Tree) (i : ColorTensorTree.Leaf (shape t)) :
    ColorTensorFocus.positiveAt (shape t) i = (vertexAt t i).positive := by
  induction t with
  | leaf v => rfl
  | tensor l r hl hr => cases i with
    | inl i => exact hl i
    | inr i => exact hr i

theorem negativeAt (t : Tree) (i : ColorTensorTree.Leaf (shape t)) :
    ColorTensorFocus.negativeAt (shape t) i = (vertexAt t i).negative := by
  induction t with
  | leaf v => rfl
  | tensor l r hl hr => cases i with
    | inl i => exact hl i
    | inr i => exact hr i

theorem vertex_certified (t : Tree) (ht : Certified t) (i : ColorTensorTree.Leaf (shape t)) :
    ColorVertexCertificates.Certified (vertexAt t i) := by
  induction t with
  | leaf v => exact ht
  | tensor l r hl hr => cases i with
    | inl i => exact hl ht.1 i
    | inr i => exact hr ht.2 i

def symmetricMap : (t : Tree) → Carrier t →ₗ[ℂ] ColorSymmetricTree.Carrier (shape t)
  | .leaf v => (SymmetricTensorTrace.projection rho v.positive v.negative).comp v.split.embed.toLinearMap
  | .tensor l r => TensorProduct.map (symmetricMap l) (symmetricMap r)

theorem symmetricMap_embed (t : Tree) (ht : Certified t) (x : Carrier t) :
    (ColorSymmetricTree.split (shape t)).embed (symmetricMap t x) = (split t).embed x := by
  induction t with
  | leaf v =>
    obtain ⟨y,hy⟩ := ht.symmetric x
    change SymmetricTensorTrace.inclusion rho v.positive v.negative
      (SymmetricTensorTrace.projection rho v.positive v.negative (v.split.embed x)) = v.split.embed x
    rw [← hy,SymmetricTensorTrace.projection_inclusion]
  | tensor l r hl hr =>
    induction x using TensorProduct.inductionOn with
    | tmul x y => exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) (hl ht.1 x) (hr ht.2 y)
    | add x y hx hy =>
      exact (((ColorSymmetricTree.split (shape (.tensor l r))).embed.toLinearMap.comp
        (symmetricMap (.tensor l r))).map_add x y).trans
          ((congrArg₂ (·+·) hx hy).trans ((split (.tensor l r)).embed.map_add x y).symm)

theorem positive_repeated_zero (t : Tree) (ht : Certified t) (k : ℕ)
    (h : ColorTensorTree.positive (shape t) = ColorTensorTree.negative (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (ColorTensorTree.negative (shape t)+3*k)))
    (a : Fin k) (ha : ¬ Function.Injective
      (SU3ContractionDiagram.triples (ColorTensorTree.negative (shape t)) k
        (ColorTreeDiagrams.positiveOwner (shape t) k h) sigma a)) :
    (ColorTreeDiagrams.positiveContraction (shape t) k h sigma).comp (split t).embed = 0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change ColorTreeDiagrams.positiveContraction (shape t) k h sigma ((split t).embed x) = 0
  rw [← symmetricMap_embed t ht x]
  exact LinearMap.congr_fun (ColorSymmetricTree.positive_repeated_zero (shape t) k h sigma a ha)
    (symmetricMap t x)

theorem negative_repeated_zero (t : Tree) (ht : Certified t) (k : ℕ)
    (h : ColorTensorTree.negative (shape t) = ColorTensorTree.positive (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (ColorTensorTree.positive (shape t)+3*k)))
    (a : Fin k) (ha : ¬ Function.Injective
      (SU3DualContractionDiagram.triples (ColorTensorTree.positive (shape t)) k
        (ColorTreeDiagrams.negativeOwner (shape t) k h) sigma a)) :
    (ColorTreeDiagrams.negativeContraction (shape t) k h sigma).comp (split t).embed = 0 := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change ColorTreeDiagrams.negativeContraction (shape t) k h sigma ((split t).embed x) = 0
  rw [← symmetricMap_embed t ht x]
  exact LinearMap.congr_fun (ColorSymmetricTree.negative_repeated_zero (shape t) k h sigma a ha)
    (symmetricMap t x)

end
end Math.ColorCertifiedTree
