import Math.LinearAlgebra.SymmetricCubeHook
import Math.RepresentationTheory.ExteriorCubeHook

/-! Equivariant symmetric-cube/exterior-hook decomposition for an arbitrary
representation, without finite dimension or irreducibility assumptions. -/
namespace Math.SymmetricCubeHookRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A)
abbrev source := r.tprod (r.symmetricPower 2)
@[reducible] local instance : AddCommGroup (SymmetricCubeHook.Source (A := A)) := inferInstance

def multiply : IntertwiningMap (source r) (r.symmetricPower 3) where
  toLinearMap := SymmetricCubeHook.multiply
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact SymmetricCubeHook.multiply_natural (r g) x

def toHook : IntertwiningMap (source r) (ExteriorCubeHookRepresentation.action r) where
  toLinearMap := SymmetricCubeHook.toHook
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact SymmetricCubeHook.toExterior_natural (r g) x

/-- The same actual exterior hook complements the symmetric cubic quotient. -/
def equivalence : Representation.Equiv (source r)
    ((r.symmetricPower 3).prod (ExteriorCubeHookRepresentation.action r)) where
  toLinearEquiv := SymmetricCubeHook.split
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (multiply r).isIntertwining _ _ g x
    · exact ((3 : ℂ)⁻¹ • toHook r).isIntertwining _ _ g x

end
end Math.SymmetricCubeHookRepresentation
