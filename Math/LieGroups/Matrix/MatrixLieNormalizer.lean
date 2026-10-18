import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Algebra.Lie.Normalizer
import Mathlib.Algebra.Lie.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Lie normalizers of Killing matrix algebras with scalar commutant

A normalizing matrix induces a derivation. Innerness then expresses it as
an element of the Lie algebra plus a scalar matrix. For a traceless algebra
of nonempty matrix size in characteristic zero, the trace-zero part of the
normalizer is exactly the original algebra.
This is an algebraic statement, not a closed-subgroup tangent theorem.
-/

set_option autoImplicit false

namespace Math.MatrixLieNormalizer

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
variable (L : LieSubalgebra K (Matrix n n K))

def derivation (A : Matrix n n K) (hA : A ∈ L.normalizer) : LieDerivation K L L where
  toFun x := ⟨⁅A, (x : Matrix n n K)⁆, (L.mem_normalizer_iff A).mp hA x x.property⟩
  map_add' x y := Subtype.ext (lie_add A _ _)
  map_smul' c x := Subtype.ext (lie_smul c A _)
  leibniz' x y := by
    apply Subtype.ext
    change ⁅A, ⁅(x : Matrix n n K), (y : Matrix n n K)⁆⁆ =
      ⁅(x : Matrix n n K), ⁅A, (y : Matrix n n K)⁆⁆ -
        ⁅(y : Matrix n n K), ⁅A, (x : Matrix n n K)⁆⁆
    rw [leibniz_lie, sub_eq_add_neg, lie_skew, add_comm]

@[simp] theorem derivation_apply (A : Matrix n n K) (hA : A ∈ L.normalizer) (x : L) :
    (derivation L A hA x : Matrix n n K) = ⁅A, (x : Matrix n n K)⁆ := rfl

variable [LieAlgebra.IsKilling K L]

/-- No irreducibility assumption is needed beyond the stated scalar commutant. -/
theorem normalizer_decomposition
    (hcomm : ∀ A : Matrix n n K, (∀ x ∈ L, ⁅A, x⁆ = 0) → ∃ c : K, A = c • 1)
    (A : Matrix n n K) (hA : A ∈ L.normalizer) :
    ∃ z : L, ∃ c : K, A = (z : Matrix n n K) + c • 1 := by
  obtain ⟨z, hz⟩ := LieDerivation.IsKilling.exists_eq_ad (derivation L A hA)
  have hc : ∀ x ∈ L, ⁅A - (z : Matrix n n K), x⁆ = 0 := by
    intro x hx
    have h := congrArg (fun D : LieDerivation K L L => (D ⟨x, hx⟩ : Matrix n n K)) hz
    change -⁅x, (z : Matrix n n K)⁆ = ⁅A, x⁆ at h
    rw [lie_skew] at h
    rw [sub_lie, h, sub_self]
  obtain ⟨c, hc⟩ := hcomm _ hc
  exact ⟨z, c, by rw [← hc]; abel⟩

variable [CharZero K] [Nonempty n]

theorem mem_of_normalizes_of_trace_zero
    (hcomm : ∀ A : Matrix n n K, (∀ x ∈ L, ⁅A, x⁆ = 0) → ∃ c : K, A = c • 1)
    (htrace : ∀ x ∈ L, Matrix.trace x = 0)
    (A : Matrix n n K) (hA : A ∈ L.normalizer) (ht : Matrix.trace A = 0) : A ∈ L := by
  obtain ⟨z, c, rfl⟩ := normalizer_decomposition L hcomm A hA
  have hn : (Fintype.card n : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Matrix.trace_add, htrace _ z.property, Matrix.trace_smul, Matrix.trace_one,
    zero_add, smul_eq_mul] at ht
  have hc : c = 0 := (mul_eq_zero.mp ht).resolve_right hn
  simpa only [hc, zero_smul, add_zero] using z.property

theorem mem_iff_normalizes_and_trace_zero
    (hcomm : ∀ A : Matrix n n K, (∀ x ∈ L, ⁅A, x⁆ = 0) → ∃ c : K, A = c • 1)
    (htrace : ∀ x ∈ L, Matrix.trace x = 0) (A : Matrix n n K) :
    A ∈ L ↔ A ∈ L.normalizer ∧ Matrix.trace A = 0 :=
  ⟨fun h => ⟨L.le_normalizer h, htrace A h⟩,
    fun h => mem_of_normalizes_of_trace_zero L hcomm htrace A h.1 h.2⟩

end

end Math.MatrixLieNormalizer
