import Math.RepresentationTheory.ColorTreeSupport

/-! Uniform, premise-free color coupling for the concrete symmetric and
trace-free factors used by the signed SM exterior branches. -/
namespace Math.RestrictedColorWordSupport
set_option autoImplicit false
noncomputable section

inductive Kind
  | symmetric (degree : ℕ)
  | oppositeSymmetric (degree : ℕ)
  | symmetricDual (degree : ℕ)
  | oppositeSymmetricDual (degree : ℕ)
  | square | cube | squareSquare | adjoint
  | oppositeSquare | oppositeCube | oppositeSquareSquare | oppositeAdjoint
  | squareDual | cubeDual | squareSquareDual | adjointDual
  | oppositeSquareDual | oppositeCubeDual | oppositeSquareSquareDual | oppositeAdjointDual

def model : Kind → ColorFlagVertex.Vertex
  | .symmetric n => ColorFlagVertex.positiveSymmetric n
  | .oppositeSymmetric n => ColorFlagVertex.negativeSymmetric n
  | .symmetricDual n => ColorFlagVertex.symmetricDual n
  | .oppositeSymmetricDual n => ColorFlagVertex.oppositeSymmetricDual n
  | .square => ColorFlagVertex.square
  | .cube => ColorFlagVertex.cube
  | .squareSquare => ColorFlagVertex.squareSquare
  | .adjoint => ColorFlagVertex.adjoint
  | .oppositeSquare => ColorFlagVertex.oppositeSquare
  | .oppositeCube => ColorFlagVertex.oppositeCube
  | .oppositeSquareSquare => ColorFlagVertex.oppositeSquareSquare
  | .oppositeAdjoint => ColorFlagVertex.oppositeAdjoint
  | .squareDual => ColorFlagVertex.squareDual
  | .cubeDual => ColorFlagVertex.cubeDual
  | .squareSquareDual => ColorFlagVertex.squareSquareDual
  | .adjointDual => ColorFlagVertex.adjointDual
  | .oppositeSquareDual => ColorFlagVertex.oppositeSquareDual
  | .oppositeCubeDual => ColorFlagVertex.oppositeCubeDual
  | .oppositeSquareSquareDual => ColorFlagVertex.oppositeSquareSquareDual
  | .oppositeAdjointDual => ColorFlagVertex.oppositeAdjointDual

theorem model_certified (k : Kind) : ColorVertexCertificates.Certified (model k) := by
  cases k with
  | symmetric n => exact ColorVertexCertificates.positiveSymmetric n
  | oppositeSymmetric n => exact ColorVertexCertificates.negativeSymmetric n
  | symmetricDual n => exact ColorVertexCertificates.symmetricDual n
  | oppositeSymmetricDual n => exact ColorVertexCertificates.oppositeSymmetricDual n
  | square => exact ColorVertexCertificates.square
  | cube => exact ColorVertexCertificates.cube
  | squareSquare => exact ColorVertexCertificates.squareSquare
  | adjoint => exact ColorVertexCertificates.adjoint
  | oppositeSquare => exact ColorVertexCertificates.oppositeSquare
  | oppositeCube => exact ColorVertexCertificates.oppositeCube
  | oppositeSquareSquare => exact ColorVertexCertificates.oppositeSquareSquare
  | oppositeAdjoint => exact ColorVertexCertificates.oppositeAdjoint
  | squareDual => exact ColorVertexCertificates.squareDual
  | cubeDual => exact ColorVertexCertificates.cubeDual
  | squareSquareDual => exact ColorVertexCertificates.squareSquareDual
  | adjointDual => exact ColorVertexCertificates.adjointDual
  | oppositeSquareDual => exact ColorVertexCertificates.oppositeSquareDual
  | oppositeCubeDual => exact ColorVertexCertificates.oppositeCubeDual
  | oppositeSquareSquareDual => exact ColorVertexCertificates.oppositeSquareSquareDual
  | oppositeAdjointDual => exact ColorVertexCertificates.oppositeAdjointDual

inductive Word
  | leaf (kind : Kind)
  | tensor (left right : Word)

def tree : Word → ColorFlagTree.Tree
  | .leaf k => .leaf (model k)
  | .tensor l r => .tensor (tree l) (tree r)

theorem certified (w : Word) : ColorCertifiedTree.Certified (tree w) := by
  induction w with
  | leaf k => exact model_certified k
  | tensor l r hl hr => exact ⟨hl,hr⟩

abbrev Carrier (w : Word) := ColorFlagTree.Carrier (tree w)
abbrev action (w : Word) := ColorFlagTree.action (tree w)
def Supports (w : Word) : Prop := ColorTreeSupport.DiagramSupport (tree w)

/-- Arbitrary products of the actual reachable color factors have a positive
finite diagram criterion, with every local certificate discharged. -/
theorem allowed_iff (w : Word) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action w)) ↔ Supports w :=
  ColorTreeSupport.allowed_iff (tree w) (certified w)

theorem forbidden_iff (w : Word) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (action w)) ↔ ¬ Supports w :=
  ColorTreeSupport.forbidden_iff (tree w) (certified w)

end
end Math.RestrictedColorWordSupport
