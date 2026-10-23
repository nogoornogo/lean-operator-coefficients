import Math.LinearAlgebra.Constructions.DistinctSpeciesBilinear
import Mathlib.LinearAlgebra.TensorProduct.Basic

open Math

/-! Ordered coefficients with two distinct fermions extend to an alternating
two-fermion coefficient. Bosons stay in the value module. -/
namespace Physics.DistinctFermionCoefficient
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

variable {L E S F : Type*}
  [AddCommGroup L] [Module ℂ L] [AddCommGroup E] [Module ℂ E]
  [AddCommGroup S] [Module ℂ S] [AddCommGroup F] [Module ℂ F]

def ordered (c : ((L ⊗[ℂ] E) ⊗[ℂ] (S ⊗[ℂ] F)) →ₗ[ℂ] ℂ) :
    L →ₗ[ℂ] E →ₗ[ℂ] ((S ⊗[ℂ] F) →ₗ[ℂ] ℂ) :=
  TensorProduct.curry (TensorProduct.curry c)

def extension (c : ((L ⊗[ℂ] E) ⊗[ℂ] (S ⊗[ℂ] F)) →ₗ[ℂ] ℂ) :=
  DistinctSpeciesBilinear.extend (ordered c)

@[simp] theorem restriction (c : ((L ⊗[ℂ] E) ⊗[ℂ] (S ⊗[ℂ] F)) →ₗ[ℂ] ℂ)
    (l : L) (e : E) (s : S) (f : F) :
    extension c (l,0) (0,e) (s ⊗ₜ[ℂ] f) = c ((l ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] f)) := by
  rw [extension, DistinctSpeciesBilinear.extend_restrict]
  rfl

theorem alternating (c : ((L ⊗[ℂ] E) ⊗[ℂ] (S ⊗[ℂ] F)) →ₗ[ℂ] ℂ)
    (x : L × E) : extension c x x = 0 := DistinctSpeciesBilinear.extend_diagonal _ x

theorem extension_injective : Function.Injective (extension (L := L) (E := E) (S := S) (F := F)) := by
  intro c d h
  apply TensorProduct.ext
  apply TensorProduct.ext
  apply LinearMap.ext; intro l
  apply LinearMap.ext; intro e
  apply TensorProduct.ext
  apply LinearMap.ext; intro s
  apply LinearMap.ext; intro f
  have he := congrArg (fun k => k (l,0) (0,e) (s ⊗ₜ[ℂ] f)) h
  simpa using he

end
end Physics.DistinctFermionCoefficient
