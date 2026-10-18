import Math.LinearAlgebra.DiagonalCentralizer
import Mathlib.LinearAlgebra.UnitaryGroup

/-! Exact group stabilizers of prescribed adjoint matrices. No minimization
or assumption that a covering product embeds injectively is used. -/
namespace Math.SUN.AdjointStabilizer
set_option autoImplicit false
noncomputable section
variable {N I J : Type*} [Fintype N] [DecidableEq N]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

abbrev Group (N : Type*) [Fintype N] [DecidableEq N] :=
  Matrix.specialUnitaryGroup N ℂ

def subgroup (V : Matrix N N ℂ) : Subgroup (Group N) where
  carrier := {g | g.val * V = V * g.val}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change (g.val * h.val) * V = V * (g.val * h.val)
    calc
      _ = g.val * (V * h.val) := by rw [Matrix.mul_assoc, hh]
      _ = (g.val * V) * h.val := (Matrix.mul_assoc _ _ _).symm
      _ = _ := by rw [hg, Matrix.mul_assoc]
  inv_mem' {g} hg := by
    have hi : g⁻¹.val * g.val = 1 := g.property.1.1
    have hr : g.val * g⁻¹.val = 1 := g.property.1.2
    change g⁻¹.val * V = V * g⁻¹.val
    calc
      _ = g⁻¹.val * V * (g.val * g⁻¹.val) := by rw [hr, Matrix.mul_one]
      _ = g⁻¹.val * (V * g.val) * g⁻¹.val := by simp only [Matrix.mul_assoc]
      _ = g⁻¹.val * (g.val * V) * g⁻¹.val := by rw [hg]
      _ = _ := by rw [← Matrix.mul_assoc g⁻¹.val g.val V, hi, Matrix.one_mul]

theorem fixed_iff (V : Matrix N N ℂ) (g : Group N) :
    g.val * V * g⁻¹.val = V ↔ g ∈ subgroup V := by
  have hr : g.val * g⁻¹.val = 1 := g.property.1.2
  have hi : g⁻¹.val * g.val = 1 := g.property.1.1
  constructor
  · intro h
    change g.val * V = V * g.val
    have he := congrArg (fun M => M * g.val) h
    simpa only [Matrix.mul_assoc, hi, Matrix.mul_one] using he
  · intro h
    change g.val * V = V * g.val at h
    rw [h, Matrix.mul_assoc, hr, Matrix.mul_one]

def vacuum (a b : ℂ) : Matrix (I ⊕ J) (I ⊕ J) ℂ :=
  Matrix.diagonal (DiagonalCentralizer.eigenvalues a b)

theorem mem_iff (a b : ℂ) (hab : a ≠ b) (g : Group (I ⊕ J)) :
    g ∈ subgroup (vacuum a b) ↔
      g.val = Matrix.fromBlocks g.val.toBlocks₁₁ 0 0 g.val.toBlocks₂₂ :=
  DiagonalCentralizer.block_form_iff g.val a b hab

theorem blocks_unitary (a b : ℂ) (hab : a ≠ b) (g : Group (I ⊕ J))
    (hg : g ∈ subgroup (vacuum a b)) :
    g.val.toBlocks₁₁ ∈ Matrix.unitaryGroup I ℂ ∧
      g.val.toBlocks₂₂ ∈ Matrix.unitaryGroup J ℂ := by
  have h := Matrix.mem_unitaryGroup_iff.mp g.property.1
  have he := (mem_iff a b hab g).mp hg
  rw [he] at h
  simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.conjTranspose_zero, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add] at h
  constructor
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    simpa [Matrix.one_apply] using congrArg (fun M => M (.inl i) (.inl j)) h
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
    ext i j
    simpa [Matrix.one_apply] using congrArg (fun M => M (.inr i) (.inr j)) h

theorem blocks_det (a b : ℂ) (hab : a ≠ b) (g : Group (I ⊕ J))
    (hg : g ∈ subgroup (vacuum a b)) :
    g.val.toBlocks₁₁.det * g.val.toBlocks₂₂.det = 1 := by
  have h := g.property.2
  change g.val.det = 1 at h
  rw [(mem_iff a b hab g).mp hg, Matrix.det_fromBlocks_zero₂₁] at h
  exact h

/-- Exact S(U(I) x U(J)) membership, with canonical blocks in both directions. -/
theorem classification (a b : ℂ) (hab : a ≠ b) (g : Group (I ⊕ J)) :
    g ∈ subgroup (vacuum a b) ↔
      ∃ A : Matrix I I ℂ, ∃ B : Matrix J J ℂ,
        A ∈ Matrix.unitaryGroup I ℂ ∧ B ∈ Matrix.unitaryGroup J ℂ ∧
        A.det * B.det = 1 ∧ g.val = Matrix.fromBlocks A 0 0 B := by
  constructor
  · intro hg
    exact ⟨_, _, (blocks_unitary a b hab g hg).1,
      (blocks_unitary a b hab g hg).2, blocks_det a b hab g hg,
      (mem_iff a b hab g).mp hg⟩
  · rintro ⟨A, B, _, _, _, he⟩
    rw [mem_iff a b hab g, he]
    simp

theorem collision (a : ℂ) : subgroup (vacuum (I := I) (J := J) a a) = ⊤ := by
  apply top_unique
  intro g hg
  exact DiagonalCentralizer.collision g.val a
end
end Math.SUN.AdjointStabilizer
