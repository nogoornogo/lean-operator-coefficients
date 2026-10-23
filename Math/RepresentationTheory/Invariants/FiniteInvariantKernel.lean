import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Exact finite group-test matrices for invariant functionals. Exhaustiveness
is an explicit generic premise, not inferred from a finite sample. -/
namespace Math.FiniteInvariantKernel
set_option autoImplicit false
noncomputable section
open Representation
variable {G V I J : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (rho : Representation ℂ G V) (b : Module.Basis J ℂ V) (tests : I → G)

def coordinates : Module.Dual ℂ V ≃ₗ[ℂ] (J → ℂ) := b.dualBasis.equivFun

@[simp] theorem coordinates_apply (f : Module.Dual ℂ V) (j : J) :
    coordinates b f j = f (b j) := Module.Basis.dualBasis_equivFun b f j

def matrix : Matrix (I × J) J ℂ := fun ij k =>
  b.repr (rho (tests ij.1) (b ij.2)) k - if k=ij.2 then 1 else 0

def constraints : (J → ℂ) →ₗ[ℂ] (I × J → ℂ) := Matrix.mulVecLin (matrix rho b tests)
abbrev Kernel := LinearMap.ker (constraints rho b tests)

omit [Fintype I] [DecidableEq I] in
theorem constraints_apply (f : Module.Dual ℂ V) (i : I) (j : J) :
    constraints rho b tests (coordinates b f) (i,j) = f (rho (tests i) (b j)) - f (b j) := by
  simp only [constraints, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    matrix, coordinates_apply]
  have he : f (rho (tests i) (b j)) =
      ∑ k, b.repr (rho (tests i) (b j)) k * f (b k) := by
    conv_lhs => rw [← b.sum_repr (rho (tests i) (b j))]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [he]
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp

omit [Fintype I] [DecidableEq I] in
theorem mem_kernel_iff (f : Module.Dual ℂ V) :
    coordinates b f ∈ Kernel rho b tests ↔ ∀ i x, f (rho (tests i) x) = f x := by
  constructor
  · intro hf i
    have he : f.comp (rho (tests i)) = f := by
      apply b.ext
      intro j
      have hj := congrFun hf (i,j)
      rw [constraints_apply] at hj
      exact sub_eq_zero.mp hj
    exact DFunLike.congr_fun he
  · intro hf
    change constraints rho b tests (coordinates b f) = 0
    funext ij
    rw [constraints_apply, hf, sub_self]
    rfl

def Exhaustive : Prop :=
  ∀ f : Module.Dual ℂ V, (∀ i x, f (rho (tests i) x) = f x) → ∀ g x, f (rho g x) = f x

def equiv (he : Exhaustive rho tests) :
    InvariantCoefficientTransport.Invariants rho ≃ₗ[ℂ] Kernel rho b tests where
  toFun f := ⟨coordinates b f.toLinearMap, (mem_kernel_iff rho b tests _).mpr
    (fun i x => f.isIntertwining _ _ (tests i) x)⟩
  invFun c :=
    { toLinearMap := (coordinates b).symm c.val
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact he _ ((mem_kernel_iff rho b tests _).mp
          (by simpa only [LinearEquiv.apply_symm_apply] using c.property)) g x }
  left_inv f := IntertwiningMap.ext ((coordinates b).symm_apply_apply f.toLinearMap)
  right_inv c := Subtype.ext ((coordinates b).apply_symm_apply c.val)
  map_add' _ _ := Subtype.ext ((coordinates b).map_add _ _)
  map_smul' z f := Subtype.ext ((coordinates b).map_smul z f.toLinearMap)

omit [Fintype I] [DecidableEq I] in
theorem allowed_iff (he : Exhaustive rho tests) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants rho) ↔
      SelectionCriteria.Allowed (Kernel rho b tests) := SelectionCriteria.allowed_equiv (equiv rho b tests he)

omit [Fintype I] [DecidableEq I] in
theorem allowed_iff_rank_lt (he : Exhaustive rho tests) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants rho) ↔
      Module.finrank ℂ (LinearMap.range (constraints rho b tests)) < Fintype.card J := by
  rw [allowed_iff rho b tests he]
  change (∃ c : Kernel rho b tests, c ≠ 0) ↔ _
  rw [← Module.finrank_pos_iff_exists_ne_zero (R := ℂ)]
  change 0 < Module.finrank ℂ (LinearMap.ker (constraints rho b tests)) ↔ _
  have hd := LinearMap.finrank_range_add_finrank_ker (constraints rho b tests)
  have hj : Module.finrank ℂ (J → ℂ) = Fintype.card J := by simp
  rw [hj] at hd
  omega

end
end Math.FiniteInvariantKernel
