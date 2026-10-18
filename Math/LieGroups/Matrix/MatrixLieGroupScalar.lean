import Math.LieGroups.Matrix.MatrixLieGroupNormalizer

/-!
# Scalar central elements in special-unitary matrix normalizers

This is a statement about the full normalizer, not its identity component.
-/

set_option autoImplicit false

namespace Math.MatrixLieGroupNormalizer

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : Type*} [Fintype n] [DecidableEq n]
variable (L : LieSubalgebra ℝ (Matrix n n ℂ))

def scalarSpecial (z : unitary ℂ) (hz : (z : ℂ) ^ Fintype.card n = 1) : Special (n := n) :=
  ⟨(z : ℂ) • 1, Unitary.smul_mem z (one_mem _), by
    change Matrix.det ((z : ℂ) • (1 : Matrix n n ℂ)) = 1
    simpa only [Matrix.det_smul, Matrix.det_one, mul_one] using hz⟩

theorem conjugate_scalarSpecial (z : unitary ℂ) (hz : (z : ℂ) ^ Fintype.card n = 1)
    (X : Matrix n n ℂ) : conjugate (scalarSpecial z hz) X = X := by
  change ((z : ℂ) • 1) * X * star ((z : ℂ) • (1 : Matrix n n ℂ)) = X
  simp only [star_smul, star_one, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, Unitary.star_mul_self_of_mem z.property, one_smul]

theorem scalarSpecial_mem (z : unitary ℂ) (hz : (z : ℂ) ^ Fintype.card n = 1) :
    scalarSpecial z hz ∈ subgroup L := by
  constructor
  · intro X hX
    simpa only [conjugate_scalarSpecial] using hX
  · intro X hX
    have hi : (scalarSpecial z hz)⁻¹ = scalarSpecial (star z)
        (by simpa only [Unitary.coe_star, star_pow, star_one] using congrArg star hz) := by
      apply Subtype.ext
      change star ((z : ℂ) • (1 : Matrix n n ℂ)) = (star (z : ℂ)) • 1
      rw [star_smul, star_one]
    rw [hi, conjugate_scalarSpecial]
    exact hX

def scalarElement (z : unitary ℂ) (hz : (z : ℂ) ^ Fintype.card n = 1) : subgroup L :=
  ⟨scalarSpecial z hz, scalarSpecial_mem L z hz⟩

@[simp] theorem scalarElement_coe (z : unitary ℂ) (hz : (z : ℂ) ^ Fintype.card n = 1) :
    ((scalarElement L z hz).val : Matrix n n ℂ) = (z : ℂ) • 1 := rfl

theorem scalarElement_mem_center (z : unitary ℂ) (hz : (z : ℂ) ^ Fintype.card n = 1) :
    scalarElement L z hz ∈ Subgroup.center (subgroup L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  apply Subtype.ext
  change (g.val : Matrix n n ℂ) * ((z : ℂ) • 1) =
    ((z : ℂ) • 1) * (g.val : Matrix n n ℂ)
  simp only [mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

theorem scalarElement_pow_coe (z : unitary ℂ) (hz : (z : ℂ) ^ Fintype.card n = 1)
    (k : ℕ) : (((scalarElement L z hz) ^ k).val : Matrix n n ℂ) = (z : ℂ) ^ k • 1 := by
  change (((Matrix.specialUnitaryGroup n ℂ).subtype.comp (subgroup L).subtype)
    (scalarElement L z hz ^ k)) = _
  rw [map_pow]
  change ((z : ℂ) • (1 : Matrix n n ℂ)) ^ k = _
  rw [smul_pow, one_pow]

end

end Math.MatrixLieGroupNormalizer
