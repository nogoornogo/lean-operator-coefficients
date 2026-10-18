import Math.RepresentationTheory.SU3ContractionDiagram
import Math.RepresentationTheory.SU3DualContractionDiagram

/-! Binary raw color tensor trees flatten by actual mixed-power equivalences.
Each leaf retains its own owner, including repeated species copies. -/
namespace Math.ColorTensorTree
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior ExternalInvariantTensor
open scoped TensorProduct

inductive Shape
  | leaf (positive negative : ℕ)
  | tensor (left right : Shape)

def Leaf : Shape → Type
  | .leaf _ _ => Unit
  | .tensor l r => Leaf l ⊕ Leaf r

instance finiteLeaf : (w : Shape) → Fintype (Leaf w)
  | .leaf _ _ => inferInstanceAs (Fintype Unit)
  | .tensor l r => by
    letI := finiteLeaf l
    letI := finiteLeaf r
    exact instFintypeSum (Leaf l) (Leaf r)

def positive : Shape → ℕ
  | .leaf p _ => p
  | .tensor l r => positive l + positive r

def negative : Shape → ℕ
  | .leaf _ q => q
  | .tensor l r => negative l + negative r

def positiveOwner : (w : Shape) → Fin (positive w) → Leaf w
  | .leaf _ _, _ => ()
  | .tensor l r, i => Fin.append
      (fun j => Sum.inl (positiveOwner l j)) (fun j => Sum.inr (positiveOwner r j)) i

def negativeOwner : (w : Shape) → Fin (negative w) → Leaf w
  | .leaf _ _, _ => ()
  | .tensor l r, i => Fin.append
      (fun j => Sum.inl (negativeOwner l j)) (fun j => Sum.inr (negativeOwner r j)) i

theorem positiveOwner_left (l r : Shape) (i : Fin (positive l)) :
    positiveOwner (.tensor l r) (Fin.castAdd (positive r) i) = Sum.inl (positiveOwner l i) :=
  Fin.append_left _ _ i

theorem positiveOwner_right (l r : Shape) (i : Fin (positive r)) :
    positiveOwner (.tensor l r) (Fin.natAdd (positive l) i) = Sum.inr (positiveOwner r i) :=
  Fin.append_right _ _ i

theorem negativeOwner_left (l r : Shape) (i : Fin (negative l)) :
    negativeOwner (.tensor l r) (Fin.castAdd (negative r) i) = Sum.inl (negativeOwner l i) :=
  Fin.append_left _ _ i

theorem negativeOwner_right (l r : Shape) (i : Fin (negative r)) :
    negativeOwner (.tensor l r) (Fin.natAdd (negative l) i) = Sum.inr (negativeOwner r i) :=
  Fin.append_right _ _ i

structure Data where
  Carrier : Type
  [additive : AddCommGroup Carrier]
  [linear : Module ℂ Carrier]
  action : Representation ℂ Group Carrier
attribute [instance] Data.additive Data.linear

def data : Shape → Data
  | .leaf p q =>
    { Carrier := SU3TensorPositive.MixedCarrier p q
      action := SU3TensorPositive.mixed p q }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (w : Shape) := (data w).Carrier
abbrev action (w : Shape) := (data w).action

def flatten : (w : Shape) → Representation.Equiv (action w)
    (SU3TensorPositive.mixed (positive w) (negative w))
  | .leaf _ _ => .refl _
  | .tensor l r => (tensorEquiv (flatten l) (flatten r)).trans
      (SU3TensorPositive.regroup (positive l) (negative l) (positive r) (negative r))

def fields : (w : Shape) → (Leaf w → Vector) → (Leaf w → Module.Dual ℂ Vector) → Carrier w
  | .leaf p q, v, f => PiTensorProduct.tprod ℂ (fun _ : Fin p => v ()) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun _ : Fin q => f ())
  | .tensor l r, v, f => fields l (v ∘ Sum.inl) (f ∘ Sum.inl) ⊗ₜ[ℂ]
      fields r (v ∘ Sum.inr) (f ∘ Sum.inr)

def rawFields : (w : Shape) → (Fin (positive w) → Vector) →
    (Fin (negative w) → Module.Dual ℂ Vector) → Carrier w
  | .leaf _ _, v, f => PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f
  | .tensor l r, v, f =>
    rawFields l (fun i => v (Fin.castAdd (positive r) i))
      (fun i => f (Fin.castAdd (negative r) i)) ⊗ₜ[ℂ]
    rawFields r (fun i => v (Fin.natAdd (positive l) i))
      (fun i => f (Fin.natAdd (negative l) i))

theorem regroup_tprod (a b c d : ℕ) (v : Fin a → Vector) (f : Fin b → Module.Dual ℂ Vector)
    (w : Fin c → Vector) (h : Fin d → Module.Dual ℂ Vector) :
    SU3TensorPositive.regroup a b c d
      ((PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) ⊗ₜ[ℂ]
        (PiTensorProduct.tprod ℂ w ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ h)) =
      PiTensorProduct.tprod ℂ (Fin.append v w) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Fin.append f h) := by
  change (_root_.TensorPower.mulEquiv (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w)) ⊗ₜ[ℂ]
    (_root_.TensorPower.mulEquiv (PiTensorProduct.tprod ℂ f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ h)) = _
  exact congrArg₂ (fun x y => x ⊗ₜ[ℂ] y)
    (_root_.TensorPower.tprod_mul_tprod ℂ v w) (_root_.TensorPower.tprod_mul_tprod ℂ f h)

theorem flatten_fields (w : Shape) (v : Leaf w → Vector) (f : Leaf w → Module.Dual ℂ Vector) :
    flatten w (fields w v f) =
      PiTensorProduct.tprod ℂ (fun i => v (positiveOwner w i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => f (negativeOwner w i)) := by
  induction w with
  | leaf p q => rfl
  | tensor l r hl hr =>
    change SU3TensorPositive.regroup (positive l) (negative l) (positive r) (negative r)
      (flatten l (fields l (v ∘ Sum.inl) (f ∘ Sum.inl)) ⊗ₜ[ℂ]
        flatten r (fields r (v ∘ Sum.inr) (f ∘ Sum.inr))) = _
    rw [hl,hr,regroup_tprod]
    congr 1
    · congr 1
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        rw [Fin.append_left]
        exact congrArg v (Fin.append_left
          (fun a => (Sum.inl (positiveOwner l a) : Leaf (.tensor l r)))
          (fun a => Sum.inr (positiveOwner r a)) j).symm
      · intro j
        rw [Fin.append_right]
        exact congrArg v (Fin.append_right
          (fun a => (Sum.inl (positiveOwner l a) : Leaf (.tensor l r)))
          (fun a => Sum.inr (positiveOwner r a)) j).symm
    · congr 1
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        rw [Fin.append_left]
        exact congrArg f (Fin.append_left
          (fun a => (Sum.inl (negativeOwner l a) : Leaf (.tensor l r)))
          (fun a => Sum.inr (negativeOwner r a)) j).symm
      · intro j
        rw [Fin.append_right]
        exact congrArg f (Fin.append_right
          (fun a => (Sum.inl (negativeOwner l a) : Leaf (.tensor l r)))
          (fun a => Sum.inr (negativeOwner r a)) j).symm

theorem flatten_rawFields (w : Shape) (v : Fin (positive w) → Vector)
    (f : Fin (negative w) → Module.Dual ℂ Vector) :
    flatten w (rawFields w v f) = PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f := by
  induction w with
  | leaf p q => rfl
  | tensor l r hl hr =>
    change SU3TensorPositive.regroup (positive l) (negative l) (positive r) (negative r)
      (flatten l (rawFields l _ _) ⊗ₜ[ℂ] flatten r (rawFields r _ _)) = _
    rw [hl,hr,regroup_tprod]
    congr 1
    · congr 1
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Fin.append]
    · congr 1
      funext i
      refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Fin.append]

end
end Math.ColorTensorTree
