import Math.LieGroups.SpecialUnitary.AdjointStabilizer

/-! Canonical group equivalence with S(U(I) x U(J)). -/
namespace Math.SUN.AdjointStabilizer
set_option autoImplicit false
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def blockPairs (I J : Type*) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] :
    Subgroup (Matrix.unitaryGroup I ℂ × Matrix.unitaryGroup J ℂ) where
  carrier := {p | p.1.val.det * p.2.val.det = 1}
  one_mem' := by simp
  mul_mem' {p q} hp hq := by
    change (p.1.val * q.1.val).det * (p.2.val * q.2.val).det = 1
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      _ = (p.1.val.det * p.2.val.det) * (q.1.val.det * q.2.val.det) := by ring
      _ = 1 := by rw [hp, hq, mul_one]
  inv_mem' {p} hp := by
    change p⁻¹.1.val.det * p⁻¹.2.val.det = 1
    have hA : p⁻¹.1.val.det * p.1.val.det = 1 := by
      rw [← Matrix.det_mul]
      simp [p.1.property.1]
    have hB : p⁻¹.2.val.det * p.2.val.det = 1 := by
      rw [← Matrix.det_mul]
      simp [p.2.property.1]
    calc
      _ = (p⁻¹.1.val.det * p⁻¹.2.val.det) * (p.1.val.det * p.2.val.det) := by
        rw [hp, mul_one]
      _ = (p⁻¹.1.val.det * p.1.val.det) * (p⁻¹.2.val.det * p.2.val.det) := by ring
      _ = 1 := by rw [hA, hB, mul_one]

def joinBlocks (p : blockPairs I J) : Group (I ⊕ J) :=
  ⟨Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val, by
    constructor
    · change Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val ∈ Matrix.unitaryGroup _ ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      have hA := Matrix.mem_unitaryGroup_iff.mp p.val.1.property
      have hB := Matrix.mem_unitaryGroup_iff.mp p.val.2.property
      simp only [Matrix.star_eq_conjTranspose] at hA hB ⊢
      simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hA, hB,
        Matrix.fromBlocks_one]
    · change (Matrix.fromBlocks p.val.1.val 0 0 p.val.2.val).det = 1
      rw [Matrix.det_fromBlocks_zero₂₁]
      exact p.property⟩

def blockEquiv (a b : ℂ) (hab : a ≠ b) :
    subgroup (vacuum (I := I) (J := J) a b) ≃* blockPairs I J where
  toFun g := ⟨(⟨g.val.val.toBlocks₁₁, (blocks_unitary a b hab g.val g.property).1⟩,
    ⟨g.val.val.toBlocks₂₂, (blocks_unitary a b hab g.val g.property).2⟩),
      blocks_det a b hab g.val g.property⟩
  invFun p := ⟨joinBlocks p, by
    rw [mem_iff a b hab]
    simp [joinBlocks]⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_iff a b hab g.val).mp g.property).symm
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> simp [joinBlocks]
  map_mul' g h := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · change (g.val.val * h.val.val).toBlocks₁₁ =
        g.val.val.toBlocks₁₁ * h.val.val.toBlocks₁₁
      rw [(mem_iff a b hab g.val).mp g.property,
        (mem_iff a b hab h.val).mp h.property]
      simp [Matrix.fromBlocks_multiply]
    · change (g.val.val * h.val.val).toBlocks₂₂ =
        g.val.val.toBlocks₂₂ * h.val.val.toBlocks₂₂
      rw [(mem_iff a b hab g.val).mp g.property,
        (mem_iff a b hab h.val).mp h.property]
      simp [Matrix.fromBlocks_multiply]

end
end Math.SUN.AdjointStabilizer
