import Math.LinearAlgebra.Exterior.ExteriorCubeDoubletCauchy
import Math.RepresentationTheory.Exterior.ExteriorCubeDoublet

/-! Equivariant cubic doublet Cauchy branching in any finite color dimension.
The color representation can itself retain arbitrary independent factors. -/
namespace Math.ExteriorCubeDoubletCauchyRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A) (j : G →* WeakDoubletScalars.Group)
open ExteriorCubeDoubletRepresentation
abbrev top := (r.exteriorPower 3).tprod ((spin j).symmetricPower 3)
@[reducible] local instance : AddCommGroup (ExteriorCubeDoubletCauchy.Top (A := A)) := inferInstance
@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Hook (V := A) ⊗[ℂ] ExteriorCubeDoublet.B) := inferInstance

def column : IntertwiningMap (top r j) (total r j) where
  toLinearMap := ExteriorSymmetricColumn.column 3
  isIntertwining' g := (ExteriorSymmetricColumn.natural 3 (r g) (spin j g)).symm

def combine : IntertwiningMap ((top r j).prod (middle r j)) (total r j) :=
  (column r j).comp (IntertwiningMap.fst ℂ _ _)+
    (hookInsert r j).comp (IntertwiningMap.snd ℂ _ _)

/-- The top and hook summands exhaust the exterior cube under the full group. -/
def equivalence [FiniteDimensional ℂ A] :
    Representation.Equiv ((top r j).prod (middle r j)) (total r j) where
  toLinearEquiv := ExteriorCubeDoubletCauchy.equivalence
  isIntertwining' := (combine r j).isIntertwining'

end
end Math.ExteriorCubeDoubletCauchyRepresentation
