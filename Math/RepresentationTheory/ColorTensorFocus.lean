import Math.RepresentationTheory.ColorSymmetricTree

/-! A labelled leaf of a binary tensor source can be varied independently.
Slot injections and substitution laws retain its actual global positions. -/
namespace Math.ColorTensorFocus
set_option autoImplicit false
noncomputable section
open Representation ColorTensorTree SU3DefiningExterior
open scoped TensorProduct

def positiveAt : (w : Shape) → Leaf w → ℕ
  | .leaf p _, _ => p
  | .tensor l _r, .inl i => positiveAt l i
  | .tensor _l r, .inr i => positiveAt r i

def negativeAt : (w : Shape) → Leaf w → ℕ
  | .leaf _ q, _ => q
  | .tensor l _r, .inl i => negativeAt l i
  | .tensor _l r, .inr i => negativeAt r i

def positiveIndex : (w : Shape) → (i : Leaf w) → Fin (positiveAt w i) → Fin (positive w)
  | .leaf _ _, _, j => j
  | .tensor l r, .inl i, j => Fin.castAdd (positive r) (positiveIndex l i j)
  | .tensor l r, .inr i, j => Fin.natAdd (positive l) (positiveIndex r i j)

def negativeIndex : (w : Shape) → (i : Leaf w) → Fin (negativeAt w i) → Fin (negative w)
  | .leaf _ _, _, j => j
  | .tensor l r, .inl i, j => Fin.castAdd (negative r) (negativeIndex l i j)
  | .tensor l r, .inr i, j => Fin.natAdd (negative l) (negativeIndex r i j)

theorem positiveOwner_index (w : Shape) (i : Leaf w) (j : Fin (positiveAt w i)) :
    positiveOwner w (positiveIndex w i j) = i := by
  induction w with
  | leaf p q => cases i; rfl
  | tensor l r hl hr =>
    cases i with
    | inl i => exact (positiveOwner_left l r _).trans (congrArg Sum.inl (hl i j))
    | inr i => exact (positiveOwner_right l r _).trans (congrArg Sum.inr (hr i j))

theorem negativeOwner_index (w : Shape) (i : Leaf w) (j : Fin (negativeAt w i)) :
    negativeOwner w (negativeIndex w i j) = i := by
  induction w with
  | leaf p q => cases i; rfl
  | tensor l r hl hr =>
    cases i with
    | inl i => exact (negativeOwner_left l r _).trans (congrArg Sum.inl (hl i j))
    | inr i => exact (negativeOwner_right l r _).trans (congrArg Sum.inr (hr i j))

theorem positive_fiber (w : Shape) (i : Leaf w) (j : Fin (positive w))
    (h : positiveOwner w j = i) : ∃ a, positiveIndex w i a = j := by
  induction w with
  | leaf p q => exact ⟨j,rfl⟩
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      refine Fin.addCases ?_ ?_ j h
      · intro a ha
        obtain ⟨b,hb⟩ := hl i a (Sum.inl.inj ((positiveOwner_left l r a).symm.trans ha))
        exact ⟨b,congrArg (Fin.castAdd (positive r)) hb⟩
      · intro a ha
        exact False.elim (Sum.inr_ne_inl ((positiveOwner_right l r a).symm.trans ha))
    | inr i =>
      refine Fin.addCases ?_ ?_ j h
      · intro a ha
        exact False.elim (Sum.inl_ne_inr ((positiveOwner_left l r a).symm.trans ha))
      · intro a ha
        obtain ⟨b,hb⟩ := hr i a (Sum.inr.inj ((positiveOwner_right l r a).symm.trans ha))
        exact ⟨b,congrArg (Fin.natAdd (positive l)) hb⟩

theorem negative_fiber (w : Shape) (i : Leaf w) (j : Fin (negative w))
    (h : negativeOwner w j = i) : ∃ a, negativeIndex w i a = j := by
  induction w with
  | leaf p q => exact ⟨j,rfl⟩
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      refine Fin.addCases ?_ ?_ j h
      · intro a ha
        obtain ⟨b,hb⟩ := hl i a (Sum.inl.inj ((negativeOwner_left l r a).symm.trans ha))
        exact ⟨b,congrArg (Fin.castAdd (negative r)) hb⟩
      · intro a ha
        exact False.elim (Sum.inr_ne_inl ((negativeOwner_right l r a).symm.trans ha))
    | inr i =>
      refine Fin.addCases ?_ ?_ j h
      · intro a ha
        exact False.elim (Sum.inl_ne_inr ((negativeOwner_left l r a).symm.trans ha))
      · intro a ha
        obtain ⟨b,hb⟩ := hr i a (Sum.inr.inj ((negativeOwner_right l r a).symm.trans ha))
        exact ⟨b,congrArg (Fin.natAdd (negative l)) hb⟩

def focus : (w : Shape) → (i : Leaf w) →
    (Leaf w → Vector) → (Leaf w → Module.Dual ℂ Vector) →
    SymmetricTensorTrace.Raw (V := Vector) (positiveAt w i) (negativeAt w i) →ₗ[ℂ]
      ColorTensorTree.Carrier w
  | .leaf _ _, _, _, _ => LinearMap.id
  | .tensor l r, .inl i, v, f =>
    ((TensorProduct.mk ℂ _ _).flip (fields r (v ∘ Sum.inr) (f ∘ Sum.inr))).comp
      (focus l i (v ∘ Sum.inl) (f ∘ Sum.inl))
  | .tensor l r, .inr i, v, f =>
    (TensorProduct.mk ℂ _ _ (fields l (v ∘ Sum.inl) (f ∘ Sum.inl))).comp
      (focus r i (v ∘ Sum.inr) (f ∘ Sum.inr))

def positiveSubstitute : (w : Shape) → (i : Leaf w) →
    (Fin (positiveAt w i) → Vector) → (Leaf w → Vector) → Fin (positive w) → Vector
  | .leaf _ _, _, x, _ => x
  | .tensor l r, .inl i, x, v => Fin.append (positiveSubstitute l i x (v ∘ Sum.inl))
      (fun j => v (Sum.inr (positiveOwner r j)))
  | .tensor l r, .inr i, x, v => Fin.append (fun j => v (Sum.inl (positiveOwner l j)))
      (positiveSubstitute r i x (v ∘ Sum.inr))

def negativeSubstitute : (w : Shape) → (i : Leaf w) →
    (Fin (negativeAt w i) → Module.Dual ℂ Vector) → (Leaf w → Module.Dual ℂ Vector) →
      Fin (negative w) → Module.Dual ℂ Vector
  | .leaf _ _, _, x, _ => x
  | .tensor l r, .inl i, x, v => Fin.append (negativeSubstitute l i x (v ∘ Sum.inl))
      (fun j => v (Sum.inr (negativeOwner r j)))
  | .tensor l r, .inr i, x, v => Fin.append (fun j => v (Sum.inl (negativeOwner l j)))
      (negativeSubstitute r i x (v ∘ Sum.inr))

theorem flatten_focus (w : Shape) (i : Leaf w)
    (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector)
    (x : Fin (positiveAt w i) → Vector) (y : Fin (negativeAt w i) → Module.Dual ℂ Vector) :
    flatten w (focus w i v f (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y)) =
      PiTensorProduct.tprod ℂ (positiveSubstitute w i x v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (negativeSubstitute w i y f) := by
  induction w with
  | leaf p q => rfl
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      exact (congrArg₂ (fun x y => SU3TensorPositive.regroup _ _ _ _ (x ⊗ₜ[ℂ] y))
        (hl i (v ∘ Sum.inl) (f ∘ Sum.inl) x y)
        (flatten_fields r (v ∘ Sum.inr) (f ∘ Sum.inr))).trans (regroup_tprod _ _ _ _ _ _ _ _)
    | inr i =>
      exact (congrArg₂ (fun x y => SU3TensorPositive.regroup _ _ _ _ (x ⊗ₜ[ℂ] y))
        (flatten_fields l (v ∘ Sum.inl) (f ∘ Sum.inl))
        (hr i (v ∘ Sum.inr) (f ∘ Sum.inr) x y)).trans (regroup_tprod _ _ _ _ _ _ _ _)

theorem append_update_left {A : Type*} (p q : ℕ) (v : Fin p → A) (f : Fin q → A)
    (j : Fin p) (e : A) :
    Fin.append (Function.update v j e) f =
      Function.update (Fin.append v f) (Fin.castAdd q j) e := by
  classical
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    simp only [Fin.append_left,Function.update_apply]
    have hi : Fin.castAdd q a = Fin.castAdd q j ↔ a = j := by
      constructor
      · intro h; exact Fin.ext (congrArg (fun z : Fin (p+q) => z.val) h)
      · exact congrArg (Fin.castAdd q)
    simp only [hi]
  · intro a
    have hi : Fin.natAdd p a ≠ Fin.castAdd q j := by
      intro h
      have hv := congrArg (fun z : Fin (p+q) => z.val) h
      change p+a.val = j.val at hv
      have hj := j.isLt
      omega
    simp only [Fin.append_right,Function.update_of_ne hi]

theorem append_update_right {A : Type*} (p q : ℕ) (v : Fin p → A) (f : Fin q → A)
    (j : Fin q) (e : A) :
    Fin.append v (Function.update f j e) =
      Function.update (Fin.append v f) (Fin.natAdd p j) e := by
  classical
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro a
    have hi : Fin.castAdd q a ≠ Fin.natAdd p j := by
      intro h
      have hv := congrArg (fun z : Fin (p+q) => z.val) h
      change a.val = p+j.val at hv
      have ha := a.isLt
      omega
    simp only [Fin.append_left,Function.update_of_ne hi]
  · intro a
    simp only [Fin.append_right,Function.update_apply]
    have hi : Fin.natAdd p a = Fin.natAdd p j ↔ a = j := by
      constructor
      · intro h
        apply Fin.ext
        have hv := congrArg (fun z : Fin (p+q) => z.val) h
        change p+a.val = p+j.val at hv
        exact Nat.add_left_cancel hv
      · exact congrArg (Fin.natAdd p)
    simp only [hi]

theorem append_owners {A B X : Type*} (p q : ℕ) (l : Fin p → A) (r : Fin q → B)
    (v : A ⊕ B → X) :
    Fin.append (fun j => v (Sum.inl (l j))) (fun j => v (Sum.inr (r j))) =
      fun j => v (Fin.append (fun a => Sum.inl (l a)) (fun a => Sum.inr (r a)) j) := by
  funext j
  refine Fin.addCases ?_ ?_ j <;> intro a <;> simp only [Fin.append_left,Fin.append_right]

theorem positiveSubstitute_index (w : Shape) (i : Leaf w)
    (x : Fin (positiveAt w i) → Vector) (v : Leaf w → Vector) (j : Fin (positiveAt w i)) :
    positiveSubstitute w i x v (positiveIndex w i j) = x j := by
  induction w with
  | leaf p q => rfl
  | tensor l r hl hr =>
    cases i with
    | inl i => exact (Fin.append_left _ _ _).trans (hl i x (v ∘ Sum.inl) j)
    | inr i => exact (Fin.append_right _ _ _).trans (hr i x (v ∘ Sum.inr) j)

theorem negativeSubstitute_index (w : Shape) (i : Leaf w)
    (x : Fin (negativeAt w i) → Module.Dual ℂ Vector) (v : Leaf w → Module.Dual ℂ Vector)
    (j : Fin (negativeAt w i)) :
    negativeSubstitute w i x v (negativeIndex w i j) = x j := by
  induction w with
  | leaf p q => rfl
  | tensor l r hl hr =>
    cases i with
    | inl i => exact (Fin.append_left _ _ _).trans (hl i x (v ∘ Sum.inl) j)
    | inr i => exact (Fin.append_right _ _ _).trans (hr i x (v ∘ Sum.inr) j)

theorem positiveSubstitute_update (w : Shape) (i : Leaf w)
    (x : Fin (positiveAt w i) → Vector) (v : Leaf w → Vector)
    (j : Fin (positiveAt w i)) (e : Vector) :
    positiveSubstitute w i (Function.update x j e) v =
      Function.update (positiveSubstitute w i x v) (positiveIndex w i j) e := by
  induction w with
  | leaf p q => rfl
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      exact (congrArg (fun f => Fin.append f (fun a => v (Sum.inr (positiveOwner r a))))
        (hl i x (v ∘ Sum.inl) j)).trans (append_update_left _ _ _ _ _ _)
    | inr i =>
      exact (congrArg (Fin.append (fun a => v (Sum.inl (positiveOwner l a))))
        (hr i x (v ∘ Sum.inr) j)).trans (append_update_right _ _ _ _ _ _)

theorem negativeSubstitute_update (w : Shape) (i : Leaf w)
    (x : Fin (negativeAt w i) → Module.Dual ℂ Vector) (v : Leaf w → Module.Dual ℂ Vector)
    (j : Fin (negativeAt w i)) (e : Module.Dual ℂ Vector) :
    negativeSubstitute w i (Function.update x j e) v =
      Function.update (negativeSubstitute w i x v) (negativeIndex w i j) e := by
  induction w with
  | leaf p q => rfl
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      exact (congrArg (fun f => Fin.append f (fun a => v (Sum.inr (negativeOwner r a))))
        (hl i x (v ∘ Sum.inl) j)).trans (append_update_left _ _ _ _ _ _)
    | inr i =>
      exact (congrArg (Fin.append (fun a => v (Sum.inl (negativeOwner l a))))
        (hr i x (v ∘ Sum.inr) j)).trans (append_update_right _ _ _ _ _ _)

theorem positive_const (w : Shape) (i : Leaf w) (v : Leaf w → Vector) :
    positiveSubstitute w i (fun _ => v i) v = fun j => v (positiveOwner w j) := by
  induction w with
  | leaf p q => cases i; rfl
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      exact (congrArg (fun f => Fin.append f (fun a => v (Sum.inr (positiveOwner r a))))
        (hl i (v ∘ Sum.inl))).trans (append_owners _ _ _ _ v)
    | inr i =>
      exact (congrArg (Fin.append (fun a => v (Sum.inl (positiveOwner l a))))
        (hr i (v ∘ Sum.inr))).trans (append_owners _ _ _ _ v)

theorem negative_const (w : Shape) (i : Leaf w) (v : Leaf w → Module.Dual ℂ Vector) :
    negativeSubstitute w i (fun _ => v i) v = fun j => v (negativeOwner w j) := by
  induction w with
  | leaf p q => cases i; rfl
  | tensor l r hl hr =>
    cases i with
    | inl i =>
      exact (congrArg (fun f => Fin.append f (fun a => v (Sum.inr (negativeOwner r a))))
        (hl i (v ∘ Sum.inl))).trans (append_owners _ _ _ _ v)
    | inr i =>
      exact (congrArg (Fin.append (fun a => v (Sum.inl (negativeOwner l a))))
        (hr i (v ∘ Sum.inr))).trans (append_owners _ _ _ _ v)

theorem positive_update (w : Shape) (i : Leaf w) (v : Leaf w → Vector)
    (j : Fin (positiveAt w i)) (e : Vector) :
    positiveSubstitute w i (Function.update (fun _ => v i) j e) v =
      Function.update (fun a => v (positiveOwner w a)) (positiveIndex w i j) e := by
  exact (positiveSubstitute_update w i (fun _ => v i) v j e).trans
    (congrArg (fun f => Function.update f (positiveIndex w i j) e) (positive_const w i v))

theorem negative_update (w : Shape) (i : Leaf w) (v : Leaf w → Module.Dual ℂ Vector)
    (j : Fin (negativeAt w i)) (e : Module.Dual ℂ Vector) :
    negativeSubstitute w i (Function.update (fun _ => v i) j e) v =
      Function.update (fun a => v (negativeOwner w a)) (negativeIndex w i j) e := by
  exact (negativeSubstitute_update w i (fun _ => v i) v j e).trans
    (congrArg (fun f => Function.update f (negativeIndex w i j) e) (negative_const w i v))

end
end Math.ColorTensorFocus
