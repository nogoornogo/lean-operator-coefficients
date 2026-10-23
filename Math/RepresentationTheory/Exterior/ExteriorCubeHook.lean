import Math.LinearAlgebra.Exterior.ExteriorCubeHook
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection
import TauCeti.RepresentationTheory.Subrepresentation

/-! Equivariant universal cubic hook splitting. No irreducibility or
finite-dimensionality hypothesis is supplied. -/
namespace Math.ExteriorCubeHookRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (r : Representation ℂ G V)

@[reducible] local instance : AddCommGroup (ExteriorCubeHook.Source (V := V)) := inferInstance
abbrev source := r.tprod (r.exteriorPower 2)

def multiply : IntertwiningMap (source r) (r.exteriorPower 3) where
  toLinearMap := ExteriorCubeHook.multiply
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro a x
    exact ExteriorCubeHook.multiply_natural (r g) a x

def coproduct : IntertwiningMap (r.exteriorPower 3) (source r) where
  toLinearMap := ExteriorCubeHook.coproduct
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorCubeHook.coproduct_natural (r g) x

abbrev hook := (multiply r).ker
abbrev action := (hook r).toRepresentation

def remainder : IntertwiningMap (source r) (source r) :=
  IntertwiningMap.id _-(3 : ℂ)⁻¹ • (coproduct r).comp (multiply r)

def project : IntertwiningMap (source r) (action r) where
  toLinearMap := ExteriorCubeHook.project
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (remainder r).isIntertwining _ _ g x

/-- A complete split of the color hook and its exterior-cube quotient. -/
def split : Representation.Equiv (source r) ((r.exteriorPower 3).prod (action r)) where
  toLinearEquiv := ExteriorCubeHook.split
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact ((3 : ℂ)⁻¹ • multiply r).isIntertwining _ _ g x
    · exact (project r).isIntertwining _ _ g x

end
end Math.ExteriorCubeHookRepresentation
