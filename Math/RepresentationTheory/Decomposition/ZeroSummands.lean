import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Prod
import Mathlib.Basic.Complex.Basic

/-! Explicit representation equivalences removing a proved zero summand.
Zero is a vector identity, not a supplied numerical dimension. -/
namespace Math.ZeroSummands
set_option autoImplicit false
noncomputable section
open Representation
variable {G A B : Type*} [Group G]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
  (r : Representation ℂ G A) (s : Representation ℂ G B)

def prodRight (hs : ∀ x : B, x=0) : Representation.Equiv (r.prod s) r where
  toLinearEquiv :=
    { toLinearMap := LinearMap.fst ℂ A B
      invFun x := (x,0)
      left_inv x := Prod.ext rfl (hs x.2).symm
      right_inv _ := rfl }
  isIntertwining' _ := rfl

def prodLeft (hr : ∀ x : A, x=0) : Representation.Equiv (r.prod s) s where
  toLinearEquiv :=
    { toLinearMap := LinearMap.snd ℂ A B
      invFun x := (0,x)
      left_inv x := Prod.ext (hr x.1).symm rfl
      right_inv _ := rfl }
  isIntertwining' _ := rfl

def equivalence (hr : ∀ x : A, x=0) (hs : ∀ x : B, x=0) : Representation.Equiv r s where
  toLinearEquiv :=
    { toLinearMap := 0
      invFun _ := 0
      left_inv x := (hr x).symm
      right_inv x := (hs x).symm }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact (map_zero (s g)).symm

end
end Math.ZeroSummands
