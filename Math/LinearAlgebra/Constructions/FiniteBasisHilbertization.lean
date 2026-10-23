import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Hilbert models from finite algebraic bases

An algebraic finite-dimensional complex vector space need not arrive with a
topology or inner product.  A chosen finite basis canonically identifies it
with a finite Euclidean coordinate space.  This file puts that structure on
an indexed copy, avoiding global orphan instances on the original type.
-/

namespace Math
namespace FiniteBasisHilbertization

noncomputable section

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {ι : Type v} [Fintype ι]

/-- An indexed copy of an algebraic vector space, whose analytic structure is
defined by the coordinates of `b`. -/
structure Copy (b : Module.Basis ι ℂ V) where
  val : V

namespace Copy

variable (b : Module.Basis ι ℂ V)

def equiv : Copy b ≃ V where
  toFun := val
  invFun := mk
  left_inv x := by cases x; rfl
  right_inv _ := rfl

instance : AddCommGroup (Copy b) :=
  (equiv b).addCommGroup

def addEquiv : Copy b ≃+ V :=
  Equiv.addEquiv (equiv b)

instance : Module ℂ (Copy b) :=
  (addEquiv b).module ℂ

/-- The algebraic identification with the original vector space. -/
def valLinearEquiv : Copy b ≃ₗ[ℂ] V :=
  (addEquiv b).linearEquiv ℂ

omit [Fintype ι] in
@[simp]
theorem valLinearEquiv_apply (x : Copy b) :
    valLinearEquiv b x = x.val :=
  rfl

omit [Fintype ι] in
@[simp]
theorem valLinearEquiv_symm_apply (x : V) :
    (valLinearEquiv b).symm x = ⟨x⟩ :=
  rfl

/-- Coordinates in the chosen basis, regarded as a Euclidean vector. -/
def coordinateEquiv : Copy b ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
  valLinearEquiv b |>.trans b.equivFun |>.trans
    (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm

@[simp]
theorem coordinateEquiv_apply_coord (x : Copy b) (i : ι) :
    WithLp.ofLp (coordinateEquiv b x) i = b.coord i x.val := by
  rfl

/-- Pull the Euclidean inner product back along the coordinate equivalence. -/
@[instance_reducible]
def innerCore : InnerProductSpace.Core ℂ (Copy b) where
  inner x y := inner ℂ (coordinateEquiv b x) (coordinateEquiv b y)
  conj_inner_symm := by
    intro x y
    exact inner_conj_symm (𝕜 := ℂ)
      (coordinateEquiv b x) (coordinateEquiv b y)
  re_inner_nonneg := by
    intro x
    exact inner_self_nonneg
  add_left := by
    intro x y z
    simp only [map_add, inner_add_left]
  smul_left := by
    intro x y c
    simp only [map_smul, inner_smul_left]
  definite := by
    intro x hx
    apply (coordinateEquiv b).injective
    simpa using (inner_self_eq_zero.mp hx)

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (Copy b) := by
  letI : InnerProductSpace.Core ℂ (Copy b) := innerCore b
  exact InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := Copy b)

noncomputable instance instInnerProductSpace : InnerProductSpace ℂ (Copy b) := by
  letI : InnerProductSpace.Core ℂ (Copy b) := innerCore b
  exact InnerProductSpace.ofCore (innerCore b).toCore

instance instFiniteDimensional : FiniteDimensional ℂ (Copy b) :=
  FiniteDimensional.of_injective (coordinateEquiv b).toLinearMap
    (coordinateEquiv b).injective

/-- The coordinate equivalence is an isometry by construction. -/
def coordinateIsometryEquiv : Copy b ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  (coordinateEquiv b).isometryOfInner (by
    intro x y
    rfl)

/-- Continuity into the copied Hilbert space is equivalent to continuity of
every algebraic basis coordinate. -/
theorem continuous_iff_coords
    {X : Type*} [TopologicalSpace X] (f : X → Copy b) :
    Continuous f ↔
      ∀ i, Continuous fun x => b.coord i (f x).val := by
  rw [← (coordinateIsometryEquiv b).comp_continuous_iff]
  constructor
  · intro hf i
    exact (PiLp.continuous_apply 2 (fun _ : ι => ℂ) i).comp hf
  · intro hf
    exact (PiLp.continuous_toLp 2 (fun _ : ι => ℂ)).comp
      (continuous_pi hf)

end Copy

end
end FiniteBasisHilbertization
end Math
