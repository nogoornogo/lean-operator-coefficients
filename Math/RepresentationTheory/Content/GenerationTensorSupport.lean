import Math.RepresentationTheory.Exterior.GenerationExteriorExhaustion
import Math.RepresentationTheory.Exterior.IndexedExteriorContent
import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Exact generation-occupation reduction under arbitrary tensor spectators.
The proof uses restriction/extension and currying, and never expands a
character or computes a dimension. -/
namespace Math.GenerationTensorSupport
set_option autoImplicit false
noncomputable section
open Representation ExteriorContentTree ExternalInvariantTensor
open scoped TensorProduct

variable {G : Type*} [Group G]

abbrev Occupation (n : ℕ) := FiniteExteriorExhaustion.Occupation (S := Fin 3) n

def generationLeaf (a : Leaf.{0} G) : Leaf.{0} G where
  Carrier := a.Carrier ⊗[ℂ] (Fin 3 → ℂ)
  rho := GenerationExteriorExhaustion.generations a.rho
  degree := a.degree

def generations : Content.{0} G → Content.{0} G
  | .leaf a => .leaf (generationLeaf a)
  | .node l r => .node (generations l) (generations r)

theorem generations_indexed (k : ℕ) (a : Fin (k+1) → Leaf.{0} G) :
    generations (IndexedExteriorContent.tree k a) =
      IndexedExteriorContent.tree k (fun i => generationLeaf (a i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Content.node (.leaf (generationLeaf (a 0)))
      (generations (IndexedExteriorContent.tree k (fun i => a i.succ))) = _
    rw [ih]
    rfl

/-- Keep the indexed dictionary abstract while transporting its entire
statistical source; concrete callers need not unfold the tensor tree. -/
def indexedDecomposition (k : ℕ) (a : Fin (k+1) → Leaf.{0} G) {n : ℕ}
    (p : Fin n → Fin (k+1))
    (hc : ∀ i, (Finset.univ.filter (fun j => p j = i)).card = (a i).degree) :
    Representation.Equiv (factor (generations (IndexedExteriorContent.tree k a)))
      (PatternExteriorSource.representation
        (fun i => GenerationExteriorExhaustion.generations (a i).rho) p) := by
  rw [generations_indexed]
  exact IndexedExteriorContent.wordDecomposition k (fun i => generationLeaf (a i)) p hc


abbrev Choice : Content.{0} G → Type
  | .leaf a => Occupation a.degree
  | .node l r => Choice l × Choice r

instance choiceFinite (t : Content.{0} G) : Fintype (Choice t) :=
  match t with
  | .leaf _ => inferInstance
  | .node l r => letI := choiceFinite l; letI := choiceFinite r; inferInstance

instance choiceDecidable (t : Content.{0} G) : DecidableEq (Choice t) :=
  match t with
  | .leaf _ => inferInstance
  | .node l r => letI := choiceDecidable l; letI := choiceDecidable r; inferInstance

def occupied : (t : Content.{0} G) → Choice t → Content.{0} G
  | .leaf a, c => IndexedExteriorContent.tree 2
      (fun i => { a with degree := (c.val i).val })
  | .node l r, c => .node (occupied l c.1) (occupied r c.2)

section Linear
variable {A B C Y : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
  [AddCommGroup Y] [Module ℂ Y]

def equivOfEq {a b : Representation ℂ G A} (h : a=b) : Representation.Equiv a b where
  toLinearEquiv := .refl ℂ A
  isIntertwining' g := by rw [h]; rfl

def precompose {a : Representation ℂ G A} {b : Representation ℂ G B}
    (e : Representation.Equiv a b) (y : Representation ℂ G Y) :
    IntertwiningMap a y ≃ₗ[ℂ] IntertwiningMap b y where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  left_inv f := by ext x; exact congrArg f (e.toLinearEquiv.symm_apply_apply x)
  right_inv f := by ext x; exact congrArg f (e.toLinearEquiv.apply_symm_apply x)
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

def associate (a : Representation ℂ G A) (b : Representation ℂ G B)
    (c : Representation ℂ G C) :
    Representation.Equiv ((a.tprod b).tprod c) (a.tprod (b.tprod c)) where
  toLinearEquiv := TensorProduct.assoc ℂ A B C
  isIntertwining' g := by ext x y z; rfl

def commute (a : Representation ℂ G A) (b : Representation ℂ G B) :
    Representation.Equiv (a.tprod b) (b.tprod a) where
  toLinearEquiv := TensorProduct.comm ℂ A B
  isIntertwining' g := by ext x y; rfl

def rotate (a : Representation ℂ G A) (b : Representation ℂ G B)
    (c : Representation ℂ G C) :
    Representation.Equiv ((a.tprod b).tprod c) (b.tprod (a.tprod c)) :=
  (tensorEquiv (commute a b) (.refl c)).trans (associate b a c)

end Linear

variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

theorem leaf_iff (a : Leaf.{0} G) (z : Representation ℂ G Z) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((factor (generations (.leaf a))).tprod z)) ↔
    ∃ c : Occupation a.degree, SelectionCriteria.Allowed
      (InvariantCoefficientTransport.Invariants ((factor (occupied (.leaf a) c)).tprod z)) := by
  rw [SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv _ z)]
  change (∃ f : IntertwiningMap ((GenerationExteriorExhaustion.generations a.rho).exteriorPower a.degree)
    z.dual, f≠0) ↔ _
  rw [GenerationExteriorExhaustion.exists_nonzero_occupation_iff]
  apply exists_congr
  intro c
  let e := IndexedExteriorContent.wordDecomposition 2
    (fun i : Fin 3 => { a with degree := (c.val i).val })
    (FiniteExteriorExhaustion.representative a.degree c)
    (fun i => congrArg Fin.val (congrFun (FiniteExteriorExhaustion.representative_counts a.degree c) i))
  exact (SelectionCriteria.allowed_equiv (precompose e z.dual)).symm.trans
    (SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv _ z)).symm

/-- All occupation choices are finite and preserve every retained group
factor jointly, also when this source is embedded in an arbitrary product. -/
theorem allowed_iff (t : Content.{0} G) : ∀ {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (z : Representation ℂ G Z),
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      ((factor (generations t)).tprod z)) ↔
    ∃ c : Choice t, SelectionCriteria.Allowed
      (InvariantCoefficientTransport.Invariants ((factor (occupied t c)).tprod z)) := by
  induction t with
  | leaf a => exact fun z => leaf_iff a z
  | node l r hl hr =>
    intro Z _ _ z
    change SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
      (((factor (generations l)).tprod (factor (generations r))).tprod z)) ↔
      ∃ c : Choice l × Choice r, SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
        (((factor (occupied l c.1)).tprod (factor (occupied r c.2))).tprod z))
    rw [SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
      (associate (factor (generations l)) (factor (generations r)) z)), hl ((factor (generations r)).tprod z)]
    constructor
    · rintro ⟨a,ha⟩
      have hb := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
        ((associate (factor (occupied l a)) (factor (generations r)) z).symm.trans
          (rotate (factor (occupied l a)) (factor (generations r)) z)))).mp ha
      obtain ⟨b,hb⟩ := (hr ((factor (occupied l a)).tprod z)).mp hb
      exact ⟨(a,b),(SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
        (rotate (factor (occupied l a)) (factor (occupied r b)) z))).mpr hb⟩
    · rintro ⟨⟨a,b⟩,hab⟩
      refine ⟨a,?_⟩
      have hb := (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
        (rotate (factor (occupied l a)) (factor (occupied r b)) z))).mp hab
      have hc := (hr ((factor (occupied l a)).tprod z)).mpr ⟨b,hb⟩
      exact (SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv
        ((associate (factor (occupied l a)) (factor (generations r)) z).symm.trans
          (rotate (factor (occupied l a)) (factor (generations r)) z)))).mpr hc

end
end Math.GenerationTensorSupport
