import Math.LieGroups.E6.Minuscule.CompactNormalizer
import Math.LieGroups.Matrix.MatrixLieGroupScalar
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# A central element of order 27 in the full compact normalizer

This rules out treating the full normalizer as a group with center of
exponent three. It does not determine the center of its identity component.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

def scalarRoot27 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 27)

theorem scalarRoot27_primitive : IsPrimitiveRoot scalarRoot27 27 :=
  Complex.isPrimitiveRoot_exp 27 (by decide)

def scalarUnitary27 : unitary ℂ := ⟨scalarRoot27, by
  have hn := scalarRoot27_primitive.norm'_eq_one (by decide)
  constructor <;> simp [Complex.conj_mul', Complex.mul_conj', hn]⟩

def centralScalar27 : compactNormalizer :=
  MatrixLieGroupNormalizer.scalarElement compactMatrixLieAlgebra scalarUnitary27
    scalarRoot27_primitive.pow_eq_one

theorem centralScalar27_mem_center : centralScalar27 ∈ Subgroup.center compactNormalizer :=
  MatrixLieGroupNormalizer.scalarElement_mem_center _ _ _

theorem centralScalar27_pow_coe (k : ℕ) :
    ((centralScalar27 ^ k).val : Matrix27) = scalarRoot27 ^ k • 1 :=
  MatrixLieGroupNormalizer.scalarElement_pow_coe _ _ _ k

theorem centralScalar27_pow_eq_one_iff (k : ℕ) : centralScalar27 ^ k = 1 ↔ 27 ∣ k := by
  rw [← scalarRoot27_primitive.pow_eq_one_iff_dvd k]
  constructor
  · intro h
    have hm := congrArg (fun g : compactNormalizer => (g.val : Matrix27)) h
    rw [centralScalar27_pow_coe] at hm
    have h00 := congrArg (fun A : Matrix27 => A 0 0) hm
    simpa using h00
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    change ((centralScalar27 ^ k).val : Matrix27) = 1
    rw [centralScalar27_pow_coe, h, one_smul]

theorem centralScalar27_orderOf : orderOf centralScalar27 = 27 := by
  exact Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one ((centralScalar27_pow_eq_one_iff 27).mpr (dvd_refl 27)))
    ((centralScalar27_pow_eq_one_iff _).mp (pow_orderOf_eq_one centralScalar27))

/-- The full normalizer fails a necessary order-three-center property. -/
theorem compactNormalizer_center_not_exponent_three :
    ¬∀ g ∈ Subgroup.center compactNormalizer, g ^ (3 : ℕ) = 1 := by
  intro h
  have hd := (centralScalar27_pow_eq_one_iff 3).mp (h _ centralScalar27_mem_center)
  norm_num at hd

/-- An explicit abstract obstruction, without postulating any compact E6 carrier. -/
theorem compactNormalizer_not_equiv_of_center_exponent_three (G : Type*) [Group G]
    (hG : ∀ g ∈ Subgroup.center G, g ^ (3 : ℕ) = 1) :
    ¬Nonempty (compactNormalizer ≃* G) := by
  rintro ⟨e⟩
  have hc : e centralScalar27 ∈ Subgroup.center G :=
    Subgroup.map_center_le_center e.surjective
      ⟨centralScalar27, centralScalar27_mem_center, rfl⟩
  have hp : centralScalar27 ^ (3 : ℕ) = 1 := e.injective (by simpa using hG _ hc)
  have hd := (centralScalar27_pow_eq_one_iff 3).mp hp
  norm_num at hd

end

end Math.E6.Minuscule
