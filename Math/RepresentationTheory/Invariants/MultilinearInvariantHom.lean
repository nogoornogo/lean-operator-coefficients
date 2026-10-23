import Math.RepresentationTheory.Tensors.ExternalInvariantTensor
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! Invariant multilinear maps as Hom from a heterogeneous tensor product. -/
namespace Math.MultilinearInvariantHom
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {H ι : Type*} [Group H] [Fintype ι]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Type*} [AddCommGroup W] [Module ℂ W]
  (r : ∀ i, Representation ℂ H (V i))

def tensorRepresentation : Representation ℂ H (⨂[ℂ] i, V i) :=
  PiTensorProduct.mapMonoidHom.comp (MonoidHom.pi r)

omit [Fintype ι] in
theorem tensorRepresentation_trivial : tensorRepresentation
    (fun i => Representation.trivial ℂ H (V i)) = Representation.trivial ℂ H (⨂[ℂ] i, V i) := by
  ext g : 1
  apply PiTensorProduct.ext
  ext v
  simp [tensorRepresentation, PiTensorProduct.map_tprod]

omit [Fintype ι] in
@[simp] theorem tensorRepresentation_tprod (g : H) (v : ∀ i, V i) :
    tensorRepresentation r g (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => r i g (v i)) := by
  simp [tensorRepresentation, PiTensorProduct.map_tprod]

def invariantMaps : Submodule ℂ (MultilinearMap ℂ V W) where
  carrier := {f | ∀ g v, f (fun i => r i g (v i)) = f v}
  zero_mem' := by intro g v; rfl
  add_mem' := by intro f h hf hh g v; exact congrArg₂ (· + ·) (hf g v) (hh g v)
  smul_mem' := by intro z f hf g v; exact congrArg (z • ·) (hf g v)

def fromMultilinear (f : invariantMaps (W := W) r) :
    IntertwiningMap (tensorRepresentation r) (Representation.trivial ℂ H W) where
  toLinearMap := PiTensorProduct.lift f.val
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simpa only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, tensorRepresentation_tprod,
      PiTensorProduct.lift.tprod, Representation.trivial_apply, LinearMap.id_apply] using
      f.property g v

def toMultilinear
    (f : IntertwiningMap (tensorRepresentation r) (Representation.trivial ℂ H W)) :
    invariantMaps (W := W) r :=
  ⟨f.toLinearMap.compMultilinearMap (PiTensorProduct.tprod ℂ), by
    intro g v
    have he := IntertwiningMap.isIntertwining _ _ f g (PiTensorProduct.tprod ℂ v)
    simpa only [LinearMap.compMultilinearMap_apply, tensorRepresentation_tprod,
      IntertwiningMap.toLinearMap_apply,
      Representation.trivial_apply, LinearMap.id_apply] using he⟩

def equiv : invariantMaps (W := W) r ≃ₗ[ℂ]
    IntertwiningMap (tensorRepresentation r) (Representation.trivial ℂ H W) where
  toFun := fromMultilinear r
  invFun := toMultilinear r
  left_inv f := by apply Subtype.ext; ext v; exact PiTensorProduct.lift.tprod _
  right_inv f := by
    apply IntertwiningMap.ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    exact PiTensorProduct.lift.tprod _
  map_add' f h := by
    apply IntertwiningMap.ext
    exact PiTensorProduct.lift.map_add f.val h.val
  map_smul' z f := by
    apply IntertwiningMap.ext
    exact PiTensorProduct.lift.map_smul z f.val

end
end Math.MultilinearInvariantHom
