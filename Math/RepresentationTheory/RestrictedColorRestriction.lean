import Math.RepresentationTheory.RestrictedColorVertices
import Math.RepresentationTheory.TraceFreeColorVertex

/-! Concrete kernel constructions commute with restriction of the group.
Their underlying linear maps and source carriers are unchanged. -/
namespace Math.RestrictedColorRestriction
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection

variable {G K V : Type*} [Group G] [Group K] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ K V) (j : G →* K)

def square : Representation.Equiv
    (SymmetricSquareContractionRepresentation.action (rho.comp j))
      ((SymmetricSquareContractionRepresentation.action rho).comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (SymmetricSquareContractionRepresentation.source (rho.comp j)) g x.val =
      (SymmetricSquareContractionRepresentation.source rho) (j g) x.val
    simp only [SymmetricSquareContractionRepresentation.source,← dual_comp rho j]
    rfl

def cube : Representation.Equiv
    (SymmetricCubeContractionRepresentation.action (rho.comp j))
      ((SymmetricCubeContractionRepresentation.action rho).comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (SymmetricCubeContractionRepresentation.source (rho.comp j)) g x.val =
      (SymmetricCubeContractionRepresentation.source rho) (j g) x.val
    simp only [SymmetricCubeContractionRepresentation.source,← dual_comp rho j]
    rfl

def squareSquare : Representation.Equiv
    (SymmetricSquarePartialTraceRepresentation.action (rho.comp j))
      ((SymmetricSquarePartialTraceRepresentation.action rho).comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (SymmetricSquarePartialTraceRepresentation.source (rho.comp j)) g x.val =
      (SymmetricSquarePartialTraceRepresentation.source rho) (j g) x.val
    simp only [SymmetricSquarePartialTraceRepresentation.source,← dual_comp rho j]
    rfl

def adjoint : Representation.Equiv
    (TraceEndomorphismSplit.traceFreeAction (rho.comp j))
      ((TraceEndomorphismSplit.traceFreeAction rho).comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply LinearMap.ext
    intro y
    change rho (j g) (x.val (rho (j g⁻¹) y)) = rho (j g) (x.val (rho ((j g)⁻¹) y))
    rw [map_inv]

omit [FiniteDimensional ℂ V] in
def symmetric (n : ℕ) : Representation.Equiv (Representation.symmetricPower (rho.comp j) n)
    ((rho.symmetricPower n).comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' _ := rfl

end
end Math.RestrictedColorRestriction
