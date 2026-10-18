import Math.RepresentationTheory.ColorFlagVertex
import Math.RepresentationTheory.SU3TensorTriality

/-! Valid color diagrams construct nonzero invariant coefficients on any
binary tree of actual vertices with proved incident-flag preimages. -/
namespace Math.ColorFlagTree
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior SplitRepresentationProjection
open scoped TensorProduct

inductive Tree
  | leaf (vertex : ColorFlagVertex.Vertex)
  | tensor (left right : Tree)

def shape : Tree → ColorTensorTree.Shape
  | .leaf v => .leaf v.positive v.negative
  | .tensor l r => .tensor (shape l) (shape r)

def data : Tree → ColorTensorTree.Data
  | .leaf v => { Carrier := v.Carrier, action := v.action }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (t : Tree) := (data t).Carrier
abbrev action (t : Tree) := (data t).action

def split : (t : Tree) → Split (ColorTensorTree.action (shape t)) (action t)
  | .leaf v => v.split
  | .tensor l r => (split l).tensor (split r)

def witness : (t : Tree) → (ColorTensorTree.Leaf (shape t) × Fin 3 → ℂ) → Carrier t
  | .leaf v, a => v.flag (ColorFlagNonvanishing.vector a ())
      (ColorFlagNonvanishing.functional a ()) (ColorFlagNonvanishing.functional_incident a ())
  | .tensor l r, a =>
    witness l (fun x => a (Sum.inl x.1,x.2)) ⊗ₜ[ℂ]
      witness r (fun x => a (Sum.inr x.1,x.2))

theorem split_witness (t : Tree) (a : ColorTensorTree.Leaf (shape t) × Fin 3 → ℂ) :
    (split t).embed (witness t a) = ColorTreeDiagrams.flags (shape t) a := by
  induction t with
  | leaf v => exact v.flag_embed _ _ _
  | tensor l r hl hr =>
    change (split l).embed (witness l (fun x => a (Sum.inl x.1,x.2))) ⊗ₜ[ℂ]
      (split r).embed (witness r (fun x => a (Sum.inr x.1,x.2))) = _
    rw [hl,hr]
    rfl

/-- Constructive sufficiency; exclusion of invalid diagrams is still needed
for the complete support iff. -/
theorem positive_allowed (t : Tree) (k : ℕ)
    (h : ColorTensorTree.positive (shape t) = ColorTensorTree.negative (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (ColorTensorTree.negative (shape t)+3*k)))
    (hv : ColorTreeDiagrams.PositiveValid (shape t) k h sigma) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action t)) := by
  obtain ⟨a,ha⟩ := (ColorTreeDiagrams.positive_flag_iff (shape t) k h sigma).mpr hv
  let F := (ColorTreeDiagrams.positiveContraction (shape t) k h sigma).comp (split t).embed
  refine ⟨F,?_⟩
  intro hf
  have he := DFunLike.congr_fun hf (witness t a)
  change ColorTreeDiagrams.positiveContraction (shape t) k h sigma
    ((split t).embed (witness t a)) = 0 at he
  rw [split_witness] at he
  exact ha he

theorem negative_allowed (t : Tree) (k : ℕ)
    (h : ColorTensorTree.negative (shape t) = ColorTensorTree.positive (shape t)+3*k)
    (sigma : Equiv.Perm (Fin (ColorTensorTree.positive (shape t)+3*k)))
    (hv : ColorTreeDiagrams.NegativeValid (shape t) k h sigma) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action t)) := by
  obtain ⟨a,ha⟩ := (ColorTreeDiagrams.negative_flag_iff (shape t) k h sigma).mpr hv
  let F := (ColorTreeDiagrams.negativeContraction (shape t) k h sigma).comp (split t).embed
  refine ⟨F,?_⟩
  intro hf
  have he := DFunLike.congr_fun hf (witness t a)
  change ColorTreeDiagrams.negativeContraction (shape t) k h sigma
    ((split t).embed (witness t a)) = 0 at he
  rw [split_witness] at he
  exact ha he

theorem triality_necessary (t : Tree)
    (h : SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action t))) :
    ColorTensorTree.positive (shape t)%3 = ColorTensorTree.negative (shape t)%3 := by
  obtain ⟨f,x,hx⟩ := (InvariantCoefficientProduct.hasUnit_iff (action t)).mpr h
  have hr : InvariantCoefficientProduct.HasUnit (ColorTensorTree.action (shape t)) :=
    ⟨f.comp (split t).project,(split t).embed x,by
      change f ((split t).project ((split t).embed x)) = 1
      rw [(split t).left_inv]
      exact hx⟩
  have hs := InvariantCoefficientProduct.transport (ColorTensorTree.flatten (shape t)) hr
  exact (SU3TensorTriality.allowed_iff _ _).mp ((InvariantCoefficientProduct.hasUnit_iff _).mp hs)

end
end Math.ColorFlagTree
