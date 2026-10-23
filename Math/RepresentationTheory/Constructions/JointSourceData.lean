import Math.RepresentationTheory.SU2.SU2PairJointPresentation
import Math.RepresentationTheory.SU2.SU2SingleJointPresentation

/-! Executable joint syntax, separated from the representation equivalences
stored in presentations. Correspondence is proved by structural degree cases. -/
namespace Math.JointSourceData
set_option autoImplicit false
open JointSourceExpression

def scalar : Expr := .atom ⟨.symmetric 0,0,0,0⟩
def color (k : RestrictedColorWordSupport.Kind) : Expr := .atom ⟨k,0,0,0⟩
def weak (n : Nat) : Expr := .atom ⟨.symmetric 0,n,0,0⟩
def spin (right : Bool) (n : Nat) : Expr :=
  if right then .atom ⟨.symmetric 0,0,0,n⟩ else .atom ⟨.symmetric 0,0,n,0⟩
def pair (right : Bool) (a b : Nat) : Expr := .tensor (weak a) (spin right b)

def single (right : Bool) : Nat → Expr
  | 0 => scalar
  | 1 => spin right 1
  | 2 => scalar
  | _+3 => .zero

def doubletPair (right : Bool) : Nat → Expr
  | 0 => pair right 0 0
  | 1 => pair right 1 1
  | 2 => .sum (pair right 2 0) (pair right 0 2)
  | 3 => pair right 1 1
  | 4 => pair right 0 0
  | _+5 => .zero

theorem single_eq (right : Bool) (n : Nat) :
    single right n = (SU2SingleJointPresentation.positive right n).expression := by
  match n with
  | 0 => cases right <;> rfl
  | 1 => cases right <;> rfl
  | 2 => cases right <;> rfl
  | _+3 => rfl

theorem doubletPair_eq (right : Bool) (n : Nat) :
    doubletPair right n = (SU2PairJointPresentation.positive right n).expression := by
  match n with
  | 0 => cases right <;> rfl
  | 1 => cases right <;> rfl
  | 2 => cases right <;> rfl
  | 3 => cases right <;> rfl
  | 4 => cases right <;> rfl
  | _+5 => rfl

/-- Data-only diagnostic; no support judgment is inferred from its output. -/
def branchCount : Expr → Nat
  | .zero => 0
  | .atom _ => 1
  | .sum l r => branchCount l + branchCount r
  | .tensor l r => branchCount l * branchCount r

end Math.JointSourceData
