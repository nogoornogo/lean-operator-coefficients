import Math.RepresentationTheory.RestrictedColorWordSupport

/-! Actual dual transport for every reachable color kind. Double duals are
removed by evaluation; opposite colors are never assumed self-dual. -/
namespace Math.RestrictedColorKindDuality
set_option autoImplicit false
noncomputable section
open Representation RestrictedColorWordSupport SplitRepresentationProjection

def dual : Kind → Kind
  | .symmetric n => .symmetricDual n
  | .oppositeSymmetric n => .oppositeSymmetricDual n
  | .symmetricDual n => .symmetric n
  | .oppositeSymmetricDual n => .oppositeSymmetric n
  | .square => .squareDual
  | .cube => .cubeDual
  | .squareSquare => .squareSquareDual
  | .adjoint => .adjointDual
  | .oppositeSquare => .oppositeSquareDual
  | .oppositeCube => .oppositeCubeDual
  | .oppositeSquareSquare => .oppositeSquareSquareDual
  | .oppositeAdjoint => .oppositeAdjointDual
  | .squareDual => .square
  | .cubeDual => .cube
  | .squareSquareDual => .squareSquare
  | .adjointDual => .adjoint
  | .oppositeSquareDual => .oppositeSquare
  | .oppositeCubeDual => .oppositeCube
  | .oppositeSquareSquareDual => .oppositeSquareSquare
  | .oppositeAdjointDual => .oppositeAdjoint

theorem involution (k : Kind) : dual (dual k) = k := by cases k <;> rfl

def removeBidual (k : Kind) : Representation.Equiv (model k).action.dual.dual (model k).action := by
  letI : Module.Finite ℂ (model k).Carrier := ColorFlagVertex.finite (model k)
  exact (bidualEquiv (model k).action).symm

def equivalence : (k : Kind) → Representation.Equiv (model k).action.dual (model (dual k)).action
  | .symmetric _ => .refl _
  | .oppositeSymmetric _ => .refl _
  | .symmetricDual n => removeBidual (.symmetric n)
  | .oppositeSymmetricDual n => removeBidual (.oppositeSymmetric n)
  | .square => .refl _
  | .cube => .refl _
  | .squareSquare => .refl _
  | .adjoint => .refl _
  | .oppositeSquare => .refl _
  | .oppositeCube => .refl _
  | .oppositeSquareSquare => .refl _
  | .oppositeAdjoint => .refl _
  | .squareDual => removeBidual .square
  | .cubeDual => removeBidual .cube
  | .squareSquareDual => removeBidual .squareSquare
  | .adjointDual => removeBidual .adjoint
  | .oppositeSquareDual => removeBidual .oppositeSquare
  | .oppositeCubeDual => removeBidual .oppositeCube
  | .oppositeSquareSquareDual => removeBidual .oppositeSquareSquare
  | .oppositeAdjointDual => removeBidual .oppositeAdjoint

end
end Math.RestrictedColorKindDuality
