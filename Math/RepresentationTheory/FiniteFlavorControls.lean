import Math.RepresentationTheory.InvariantPairing
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Exact small non-Abelian flavor controls

The sum-zero permutation spaces give actual two- and three-dimensional
complex representations of S3 and A4. These are algebraic controls, not
UV models or an exhaustive scan of flavor assignments.
-/

set_option autoImplicit false

namespace Math.FiniteFlavorControls

noncomputable section

open scoped BigOperators TensorProduct

def permutation (n : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) (Fin n → ℂ) where
  toFun g :=
    { toFun := fun x i => x (g⁻¹ i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext x i; simp
  map_mul' := by intros; ext x i; simp

def coordinateSum (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun x := ∑ i, x i
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

def sumIntertwiner (n : ℕ) : Representation.IntertwiningMap (permutation n)
    (Representation.trivial ℂ (Equiv.Perm (Fin n)) ℂ) where
  toLinearMap := coordinateSum n
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact Equiv.sum_comp g.symm x

abbrev SumZero (n : ℕ) := (sumIntertwiner n).ker.toSubmodule

def standard (n : ℕ) : Representation ℂ (Equiv.Perm (Fin n)) (SumZero n) :=
  (sumIntertwiner n).ker.toRepresentation

@[simp] theorem standard_apply {n : ℕ} (g : Equiv.Perm (Fin n))
    (x : SumZero n) (i : Fin n) : (standard n g x).val i = x.val (g⁻¹ i) := rfl

/-- Restriction of the standard Hermitian form is preserved exactly. -/
theorem standard_preserves_hermitian {n : ℕ} (g : Equiv.Perm (Fin n))
    (x y : SumZero n) :
    (∑ i, star ((standard n g x).val i) * (standard n g y).val i) =
      ∑ i, star (x.val i) * y.val i :=
  Equiv.sum_comp g.symm (fun i => star (x.val i) * y.val i)

theorem sumZero_finrank (n : ℕ) : Module.finrank ℂ (SumZero (n + 1)) = n := by
  have hs : Function.Surjective (coordinateSum (n + 1)) := by
    intro z
    exact ⟨Pi.single 0 z, by simp [coordinateSum]⟩
  have he := (coordinateSum (n + 1)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs] at he
  have hk : (sumIntertwiner (n + 1)).ker.toSubmodule =
      LinearMap.ker (coordinateSum (n + 1)) := rfl
  change Module.finrank ℂ (sumIntertwiner (n + 1)).ker.toSubmodule = n
  rw [hk]
  have he' : 1 + Module.finrank ℂ (coordinateSum (n + 1)).ker = n + 1 := by
    simpa using he
  omega

def difference {n : ℕ} (i j : Fin n) : SumZero n :=
  ⟨Pi.single i 1 - Pi.single j 1, by
    change (coordinateSum n) _ = 0
    simp [coordinateSum, Finset.sum_sub_distrib]⟩

theorem difference_ne_zero {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    difference i j ≠ 0 := by
  intro hz
  have he := congrArg (fun x : SumZero n => x.val i) hz
  simp [difference, h] at he

theorem sum_differences {n : ℕ} (j : Fin n) (x : SumZero n) :
    (∑ i, x.val i • difference i j) = x := by
  apply Subtype.ext
  have hx : ∑ i, x.val i = 0 := x.property
  ext a
  simp [difference, Pi.single_apply, mul_sub, Finset.sum_sub_distrib, hx]

/-- A generator that reverses every spanning difference kills all invariant
linear functionals. This is a control, not a four-fermion no-go. -/
theorem invariantFunctional_eq_zero {n : ℕ} {H : Type*} [Group H]
    (j : Fin n) (i : H →* Equiv.Perm (Fin n))
    (hf : ∀ a, ∃ g : H, (standard n) (i g) (difference a j) = -difference a j)
    (f : Representation.IntertwiningMap ((standard n).comp i)
      (Representation.trivial ℂ H ℂ)) : f = 0 := by
  have hz (a : Fin n) : f (difference a j) = 0 := by
    obtain ⟨g, hg⟩ := hf a
    have he := congrArg (fun l => l (difference a j)) (f.isIntertwining' g)
    change f ((standard n) (i g) (difference a j)) = f (difference a j) at he
    rw [hg, map_neg] at he
    linear_combination -he / 2
  ext x
  rw [← sum_differences j x, map_sum]
  simp [hz]

abbrev S3 := Equiv.Perm (Fin 3)
abbrev A4 := alternatingGroup (Fin 4)

def s3 : Representation ℂ S3 (SumZero 3) := standard 3
def a4 : Representation ℂ A4 (SumZero 4) :=
  (standard 4).comp (alternatingGroup (Fin 4)).subtype

theorem s3_dimension : Module.finrank ℂ (SumZero 3) = 2 := sumZero_finrank 2
theorem a4_dimension : Module.finrank ℂ (SumZero 4) = 3 := sumZero_finrank 3

instance : Nontrivial (SumZero 3) :=
  ⟨⟨difference 1 0, 0, difference_ne_zero 1 0 (by decide)⟩⟩
instance : Nontrivial (SumZero 4) :=
  ⟨⟨difference 1 0, 0, difference_ne_zero 1 0 (by decide)⟩⟩

theorem s3_noncommuting :
    (Equiv.swap 0 1 : S3) * Equiv.swap 1 2 ≠ Equiv.swap 1 2 * Equiv.swap 0 1 := by
  decide

def a4Flip1 : A4 := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
def a4Flip2 : A4 := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by simp [Equiv.Perm.mem_alternatingGroup]⟩
def a4Flip3 : A4 := ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩
def a4Cycle : A4 := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by simp [Equiv.Perm.mem_alternatingGroup]⟩

theorem a4_noncommuting : a4Flip1 * a4Cycle ≠ a4Cycle * a4Flip1 := by decide

theorem s3_no_invariant_functional
    (f : Representation.IntertwiningMap s3 (Representation.trivial ℂ S3 ℂ)) : f = 0 := by
  apply invariantFunctional_eq_zero (0 : Fin 3) (MonoidHom.id S3) ?_ f
  intro a
  refine ⟨Equiv.swap a 0, ?_⟩
  apply Subtype.ext
  ext b
  change (difference a 0).val ((Equiv.swap a 0)⁻¹ b) = -(difference a 0).val b
  fin_cases a <;> fin_cases b <;> norm_num [difference, Equiv.swap_apply_def, Pi.single_apply]

theorem a4_no_invariant_functional
    (f : Representation.IntertwiningMap a4 (Representation.trivial ℂ A4 ℂ)) : f = 0 := by
  apply invariantFunctional_eq_zero (0 : Fin 4) (alternatingGroup (Fin 4)).subtype ?_ f
  intro a
  fin_cases a
  · exact ⟨1, by apply Subtype.ext; simp [difference]⟩
  · refine ⟨a4Flip1, ?_⟩
    apply Subtype.ext
    ext b
    change (difference 1 0).val ((a4Flip1.val)⁻¹ b) = -(difference 1 0).val b
    fin_cases b <;> norm_num [difference, a4Flip1, Equiv.swap_apply_def, Pi.single_apply, Fin.ext_iff]
  · refine ⟨a4Flip2, ?_⟩
    apply Subtype.ext
    ext b
    change (difference 2 0).val ((a4Flip2.val)⁻¹ b) = -(difference 2 0).val b
    fin_cases b <;> norm_num [difference, a4Flip2, Equiv.swap_apply_def, Pi.single_apply, Fin.ext_iff]
  · refine ⟨a4Flip3, ?_⟩
    apply Subtype.ext
    ext b
    change (difference 3 0).val ((a4Flip3.val)⁻¹ b) = -(difference 3 0).val b
    fin_cases b <;> norm_num [difference, a4Flip3, Equiv.swap_apply_def, Pi.single_apply, Fin.ext_iff]

theorem s3_pairedCoefficient_ne_zero : InvariantPairing.pairedCoefficient s3 s3 ≠ 0 :=
  InvariantPairing.pairedCoefficient_ne_zero s3 s3

theorem a4_pairedCoefficient_ne_zero : InvariantPairing.pairedCoefficient a4 a4 ≠ 0 :=
  InvariantPairing.pairedCoefficient_ne_zero a4 a4

section Unmatched

variable {H E : Type*} [Group H] [AddCommGroup E] [Module ℂ E]
  (rho : Representation ℂ H E)

/-- A four-factor negative control: one nontrivial factor and three singlets. -/
def withThreeTrivial :=
  ((rho.tprod (Representation.trivial ℂ H ℂ)).tprod
    (Representation.trivial ℂ H ℂ)).tprod (Representation.trivial ℂ H ℂ)

def discardThreeTrivial : Representation.Equiv (withThreeTrivial rho) rho :=
  ((Representation.TensorProduct.rid ℂ _).trans
    (Representation.TensorProduct.rid ℂ _)).trans (Representation.TensorProduct.rid ℂ rho)

theorem withThreeTrivial_no_invariant
    (h : ∀ f : Representation.IntertwiningMap rho (Representation.trivial ℂ H ℂ), f = 0)
    (f : Representation.IntertwiningMap (withThreeTrivial rho)
      (Representation.trivial ℂ H ℂ)) : f = 0 := by
  have hf := h (f.comp (discardThreeTrivial rho).symm.toIntertwiningMap)
  apply DFunLike.ext
  intro z
  have hz := congrArg (fun l => l (discardThreeTrivial rho z)) hf
  simpa using hz

end Unmatched

theorem s3_unmatched_four_no_invariant
    (f : Representation.IntertwiningMap (withThreeTrivial s3)
      (Representation.trivial ℂ S3 ℂ)) : f = 0 :=
  withThreeTrivial_no_invariant s3 s3_no_invariant_functional f

theorem a4_unmatched_four_no_invariant
    (f : Representation.IntertwiningMap (withThreeTrivial a4)
      (Representation.trivial ℂ A4 ℂ)) : f = 0 :=
  withThreeTrivial_no_invariant a4 a4_no_invariant_functional f

end
end Math.FiniteFlavorControls
