import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaDiagonal
import Math.LinearAlgebra.Matrix.MajoranaUnitaryClassification

open Math

/-! Full-unitary coordinates for the actual diagonal Majorana form used by
the specified-flavor interface. No arbitrary-matrix diagonalization is assumed. -/
namespace Physics.FlavorMajoranaUnitary
set_option autoImplicit false
noncomputable section
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def action : Representation ℂ (unitaryGroup I ℂ) (I → ℂ) where
  toFun := Matrix.UnitaryGroup.toLin'
  map_one' := Matrix.UnitaryGroup.toLin'_one
  map_mul' U V := Matrix.UnitaryGroup.toLin'_mul U V

theorem form_matrix (c : I → ℂ) :
    FlavorMajoranaDiagonal.form c = (diagonal c).toBilin' := by
  apply LinearMap.ext; intro x
  apply LinearMap.ext; intro y
  simp only [FlavorMajoranaDiagonal.form_apply, Matrix.toBilin'_apply]
  simp only [Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def subgroup (c : I → ℂ) : Subgroup (unitaryGroup I ℂ) :=
  FlavorStabilizer.massSubgroup action (FlavorMajoranaDiagonal.form c)

theorem subgroup_eq (c : I → ℂ) : subgroup c = UnitaryDiagonalCongruence.subgroup c := by
  ext U
  change U ∈ FlavorStabilizer.massSubgroup action (FlavorMajoranaDiagonal.form c) ↔
    UnitaryDiagonalCongruence.Preserves c U.val
  rw [FlavorStabilizer.mass_mem_iff, form_matrix, UnitaryDiagonalCongruence.bilinear_iff]
  rfl

def classification (c : I → ℂ) : subgroup c ≃* MajoranaUnitaryClassification.Coordinates c :=
  (MulEquiv.subgroupCongr (subgroup_eq c)).trans (MajoranaUnitaryClassification.classification c)

def residualHomEquiv {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (c : I → ℂ)
    (a : Representation ℂ (subgroup c) V) (b : Representation ℂ (subgroup c) W) :
    Representation.IntertwiningMap
      (a.comp (classification c).symm.toMonoidHom)
      (b.comp (classification c).symm.toMonoidHom) ≃ₗ[ℂ]
        Representation.IntertwiningMap a b :=
  SurjectiveHomTransport.homEquiv (classification c).symm.toMonoidHom
    (classification c).symm.surjective a b

theorem residual_nonzero_iff {V W : Type*} [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W] (c : I → ℂ)
    (a : Representation ℂ (subgroup c) V) (b : Representation ℂ (subgroup c) W) :
    (∃ f : Representation.IntertwiningMap
      (a.comp (classification c).symm.toMonoidHom)
      (b.comp (classification c).symm.toMonoidHom), f ≠ 0) ↔
        ∃ f : Representation.IntertwiningMap a b, f ≠ 0 :=
  SurjectiveHomTransport.nonzero_iff (classification c).symm.toMonoidHom
    (classification c).symm.surjective a b

end
end Physics.FlavorMajoranaUnitary
