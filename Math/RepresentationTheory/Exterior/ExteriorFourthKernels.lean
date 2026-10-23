import Math.LinearAlgebra.Exterior.ExteriorFourthKernels
import Math.RepresentationTheory.Exterior.ExteriorCubeHook

/-! The quartic multiplication quotients and their kernel complements retain
every factor of an arbitrary group action. No irreducibility is assumed. -/
namespace Math.ExteriorFourthKernelsRepresentation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
namespace K
export ExteriorFourthKernels (Source13 Source22 Fourth K211 K22)
end K

@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G A : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  (r : Representation ℂ G A)

@[reducible] local instance : AddCommGroup (K.Source22 (A := A)) :=
  Module.addCommMonoidToAddCommGroup ℂ

abbrev source13 := r.tprod (r.exteriorPower 3)
abbrev source22 := (r.exteriorPower 2).symmetricPower 2

def multiply13 : IntertwiningMap (source13 r) (r.exteriorPower 4) where
  toLinearMap := ExteriorFourthKernels.multiply13
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro a x
    exact ExteriorFourthKernels.multiply13_natural (r g) a x

def multiply22 : IntertwiningMap (source22 r) (r.exteriorPower 4) where
  toLinearMap := ExteriorFourthKernels.multiply22
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorFourthKernels.multiply22_natural (r g) x

def coproduct13 : IntertwiningMap (r.exteriorPower 4) (source13 r) where
  toLinearMap := ExteriorFourthKernels.coproduct13
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorFourthKernels.coproduct13_natural (r g) x

def coproduct22 : IntertwiningMap (r.exteriorPower 4) (source22 r) where
  toLinearMap := ExteriorFourthKernels.coproduct22
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact ExteriorFourthKernels.coproduct22_natural (r g) x

abbrev kernel211 := (multiply13 r).ker
abbrev kernel22 := (multiply22 r).ker
abbrev action211 := (kernel211 r).toRepresentation
abbrev action22 := (kernel22 r).toRepresentation

def section13 : IntertwiningMap (r.exteriorPower 4) (source13 r) :=
  (24 : ℂ)⁻¹ • coproduct13 r

def section22 : IntertwiningMap (r.exteriorPower 4) (source22 r) :=
  (24 : ℂ)⁻¹ • coproduct22 r

def remainder13 : IntertwiningMap (source13 r) (source13 r) :=
  IntertwiningMap.id _-(section13 r).comp (multiply13 r)

def remainder22 : IntertwiningMap (source22 r) (source22 r) :=
  IntertwiningMap.id _-(section22 r).comp (multiply22 r)

def project211 : IntertwiningMap (source13 r) (action211 r) where
  toLinearMap := ExteriorFourthKernels.project211
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (remainder13 r).isIntertwining _ _ g x

def project22 : IntertwiningMap (source22 r) (action22 r) where
  toLinearMap := ExteriorFourthKernels.project22
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (remainder22 r).isIntertwining _ _ g x

def split13 : Representation.Equiv (source13 r)
    ((r.exteriorPower 4).prod (action211 r)) where
  toLinearEquiv := ExteriorFourthKernels.split13
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (multiply13 r).isIntertwining _ _ g x
    · exact (project211 r).isIntertwining _ _ g x

def split22 : Representation.Equiv (source22 r)
    ((r.exteriorPower 4).prod (action22 r)) where
  toLinearEquiv := ExteriorFourthKernels.split22
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact (multiply22 r).isIntertwining _ _ g x
    · exact (project22 r).isIntertwining _ _ g x

end
end Math.ExteriorFourthKernelsRepresentation
