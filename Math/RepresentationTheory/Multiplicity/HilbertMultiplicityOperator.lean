import Math.RepresentationTheory.Multiplicity.MultiplicityMatrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Multiplicity matrices as operators on Hilbert sums

Matrices mix the copies of each constituent and act identically on the
constituent itself. This file identifies the actual Hilbert-space adjoint,
rather than merely assigning a star operation to an abstractly isomorphic
algebra. The actual determinant is computed in `HilbertMultiplicityDeterminant`.
-/

namespace Math.HilbertMultiplicityOperator

noncomputable section

variable {I : Type*} [Fintype I]
  (m : I → ℕ) (S : I → Type*)
  [∀ i, NormedAddCommGroup (S i)] [∀ i, InnerProductSpace ℂ (S i)]

abbrev Space := PiLp 2 fun i => PiLp 2 fun _ : Fin (m i) => S i
abbrev Matrices := Π i, Matrix (Fin (m i)) (Fin (m i)) ℂ

/-- The scalar matrix action on the copies of each actual constituent. -/
def mix (A : Matrices m) : Space m S →ₗ[ℂ] Space m S where
  toFun x := WithLp.toLp 2 fun i => WithLp.toLp 2 fun a => ∑ b, A i a b • x i b
  map_add' x y := by
    ext i a
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' z x := by
    ext i a
    change (∑ b, A i a b • (z • x i b)) = z • ∑ b, A i a b • x i b
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro b _
    exact smul_comm _ _ _

omit [Fintype I] in
@[simp]
theorem mix_apply (A : Matrices m) (x : Space m S) (i : I) (a : Fin (m i)) :
    mix m S A x i a = ∑ b, A i a b • x i b := rfl

omit [Fintype I] in
theorem mix_one : mix m S 1 = 1 := by
  ext x i a
  simp [Matrix.one_apply]

omit [Fintype I] in
theorem mix_mul (A B : Matrices m) : mix m S (A * B) = mix m S A * mix m S B := by
  ext x i a
  simp only [mix_apply, Module.End.mul_apply, Pi.mul_apply, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

variable [∀ i, FiniteDimensional ℂ (S i)]

instance spaceComplete : CompleteSpace (Space m S) := FiniteDimensional.complete ℂ _

/-- Multiplicity amplification as an algebra homomorphism of continuous operators. -/
def operator : Matrices m →ₐ[ℂ] (Space m S →L[ℂ] Space m S) where
  toFun A := (mix m S A).toContinuousLinearMap
  map_one' := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun f : Module.End ℂ (Space m S) => f x) (mix_one m S)
  map_mul' A B := by
    apply ContinuousLinearMap.ext
    intro x
    exact congrArg (fun f : Module.End ℂ (Space m S) => f x) (mix_mul m S A B)
  map_zero' := by ext x i a; simp
  map_add' A B := by ext x i a; simp [add_smul, Finset.sum_add_distrib]
  commutes' z := by ext x i a; simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]

@[simp]
theorem operator_apply (A : Matrices m) (x : Space m S) (i : I) (a : Fin (m i)) :
    operator m S A x i a = ∑ b, A i a b • x i b := rfl

/-- The true adjoint of the amplification is the amplified conjugate transpose. -/
theorem inner_operator (A : Matrices m) (x y : Space m S) :
    inner ℂ (operator m S (star A) x) y = inner ℂ x (operator m S A y) := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [operator_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Pi.star_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, starRingEnd_apply,
    star_star]
  exact Finset.sum_comm

theorem operator_star (A : Matrices m) : operator m S (star A) = star (operator m S A) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  exact (inner_operator m S A x y).trans
    ((operator m S A).adjoint_inner_left y x).symm

theorem operator_injective [∀ i, Nontrivial (S i)] : Function.Injective (operator m S) := by
  classical
  intro A B h
  funext i a b
  obtain ⟨v, hv⟩ := exists_ne (0 : S i)
  let x : Space m S := PiLp.single 2 i (PiLp.single 2 b v)
  have hx := congrArg (fun T : Space m S →L[ℂ] Space m S => T x i a) h
  simp [x, operator_apply] at hx
  exact (smul_left_injective ℂ hv) hx

theorem operator_mem_unitary_iff [∀ i, Nontrivial (S i)] (A : Matrices m) :
    operator m S A ∈ unitary (Space m S →L[ℂ] Space m S) ↔
      ∀ i, A i ∈ Matrix.unitaryGroup (Fin (m i)) ℂ := by
  simp only [Unitary.mem_iff, ← operator_star, ← map_mul, ← (operator m S).map_one]
  change (operator m S (star A * A) = operator m S 1 ∧
    operator m S (A * star A) = operator m S 1) ↔ _
  rw [(operator_injective m S).eq_iff, (operator_injective m S).eq_iff]
  exact ⟨fun h i => ⟨congrFun h.1 i, congrFun h.2 i⟩,
    fun h => ⟨funext fun i => (h i).1, funext fun i => (h i).2⟩⟩

theorem continuous_operator : Continuous (operator m S) :=
  (operator m S).toLinearMap.continuous_of_finiteDimensional

theorem isClosedEmbedding_operator [∀ i, Nontrivial (S i)] :
    Topology.IsClosedEmbedding (operator m S) :=
  (operator m S).toLinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (operator_injective m S))

end

end Math.HilbertMultiplicityOperator
