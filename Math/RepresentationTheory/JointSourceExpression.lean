import Math.RepresentationTheory.JointColorSpinWord
import Math.RepresentationTheory.FiniteSourceSums
import Math.RepresentationTheory.FiniteProductHomSupport

/-! Finite sums and tensors of actual joint color/weak/left/right sources.
Each summand choice is kept joint through the complete decomposition. -/
namespace Math.JointSourceExpression
set_option autoImplicit false
noncomputable section
open Representation JointColorSpinWord ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct

inductive Expr
  | zero
  | atom (label : Atom)
  | sum (left right : Expr)
  | tensor (left right : Expr)

def Choice : Expr → Type
  | .zero => Empty
  | .atom _ => Unit
  | .sum l r => Choice l ⊕ Choice r
  | .tensor l r => Choice l × Choice r

instance finiteChoice : (e : Expr) → Fintype (Choice e)
  | .zero => inferInstanceAs (Fintype Empty)
  | .atom _ => inferInstanceAs (Fintype Unit)
  | .sum l r => by
    letI := finiteChoice l
    letI := finiteChoice r
    exact instFintypeSum (Choice l) (Choice r)
  | .tensor l r => by
    letI := finiteChoice l
    letI := finiteChoice r
    exact inferInstanceAs (Fintype (Choice l × Choice r))

instance decidableChoice : (e : Expr) → DecidableEq (Choice e)
  | .zero => inferInstanceAs (DecidableEq Empty)
  | .atom _ => inferInstanceAs (DecidableEq Unit)
  | .sum l r => by
    letI := decidableChoice l
    letI := decidableChoice r
    exact inferInstanceAs (DecidableEq (Choice l ⊕ Choice r))
  | .tensor l r => by
    letI := decidableChoice l
    letI := decidableChoice r
    exact inferInstanceAs (DecidableEq (Choice l × Choice r))

instance emptyChoice : IsEmpty (Choice .zero) := inferInstanceAs (IsEmpty Empty)

def word : (e : Expr) → Choice e → Word
  | .zero, i => Empty.elim i
  | .atom a, _ => .leaf a
  | .sum l _r, .inl i => word l i
  | .sum _l r, .inr i => word r i
  | .tensor l r, i => .tensor (word l i.1) (word r i.2)

def data : Expr → JointColorSpinWord.Data
  | .zero => { Carrier := Fin 0 → ℂ, action := trivial ℂ Group (Fin 0 → ℂ) }
  | .atom a => JointColorSpinWord.data (.leaf a)
  | .sum l r =>
    { Carrier := (data l).Carrier × (data r).Carrier
      action := (data l).action.prod (data r).action }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (e : Expr) := (data e).Carrier
instance zeroSubsingleton : Subsingleton (Carrier .zero) := inferInstanceAs (Subsingleton (Fin 0 → ℂ))
abbrev action (e : Expr) := (data e).action
abbrev piece (e : Expr) (i : Choice e) := JointColorSpinWord.action (word e i)

def decomposition : (e : Expr) → Representation.Equiv (action e) (FiniteBlockHom.action (piece e))
  | .zero =>
    { toLinearEquiv := LinearEquiv.ofSubsingleton _ _
      isIntertwining' _ := by apply LinearMap.ext; intro x; exact Subsingleton.elim _ _ }
  | .atom a => FiniteSourceSums.singleton (JointColorSpinWord.action (.leaf a))
  | .sum l r =>
    (prodEquiv (decomposition l) (decomposition r)).trans
      ((FiniteSourceSums.sumEquivalence (piece l) (piece r)).trans
        (FiniteExternalProducts.along (fun i : Choice l ⊕ Choice r =>
          show Representation.Equiv (FiniteSourceSums.sumAction (piece l) (piece r) i)
            (piece (.sum l r) i) from by cases i <;> exact .refl _)))
  | .tensor l r =>
    (tensorEquiv (decomposition l) (decomposition r)).trans
      (FiniteExternalProducts.diagonalEquivalence (piece l) (piece r))

def Supports (e : Expr) : Prop := ∃ i : Choice e, JointColorSpinWord.Supports (word e i)

theorem allowed_iff (e : Expr) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action e)) ↔ Supports e := by
  rw [SelectionCriteria.allowed_equiv (InvariantCoefficientTransport.alongEquiv (decomposition e)),
    FiniteProductHomSupport.allowed_iff]
  exact exists_congr (fun i => JointColorSpinWord.allowed_iff (word e i))

theorem forbidden_iff (e : Expr) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (action e)) ↔ ¬ Supports e := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff]

def withHiggs (e : Expr) (m : ℕ) : Expr := .tensor e (.atom ⟨.symmetric 0,m,0,0⟩)

def zeroEquivalence {A : Type*} [AddCommMonoid A] [Module ℂ A]
    (rho : Representation ℂ Group A) (h : ∀ x : A, x=0) : Representation.Equiv rho (action .zero) := by
  letI : Subsingleton A := ⟨fun x y => (h x).trans (h y).symm⟩
  exact
    { toLinearEquiv := LinearEquiv.ofSubsingleton _ _
      isIntertwining' _ := by apply LinearMap.ext; intro x; exact Subsingleton.elim _ _ }

end
end Math.JointSourceExpression
