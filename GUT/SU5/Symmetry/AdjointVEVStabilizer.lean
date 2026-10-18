import GUT.SU5.Embeddings.StandardModel
import Math.LieGroups.SpecialUnitary.AdjointStabilizer
import Mathlib.LinearAlgebra.Matrix.Trace

open Math

/-! Exact stabilizer of the specified traceless SU(5) adjoint VEV. This is a
group-level statement, not a vacuum-potential or mass-spectrum calculation. -/
namespace GUT.SU5.AdjointVEVStabilizer
set_option autoImplicit false
noncomputable section
open StandardModelEmbedding

def split (g : TargetGroup) : SUN.AdjointStabilizer.Group BlockIndex :=
  ⟨Matrix.reindex blockIndexEquiv.symm blockIndexEquiv.symm g.val, by
    constructor
    · change Matrix.reindex blockIndexEquiv.symm blockIndexEquiv.symm g.val ∈
        Matrix.unitaryGroup BlockIndex ℂ
      rw [Matrix.mem_unitaryGroup_iff]
      have hu := Matrix.mem_unitaryGroup_iff.mp g.property.1
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
      change (Matrix.reindexRingEquiv ℂ blockIndexEquiv.symm) g.val *
        (Matrix.reindexRingEquiv ℂ blockIndexEquiv.symm) (star g.val) = 1
      rw [← map_mul, hu, map_one]
    · change Matrix.det (Matrix.reindex blockIndexEquiv.symm blockIndexEquiv.symm
        g.val) = 1
      rw [Matrix.det_reindex_self]
      exact g.property.2⟩

def vev : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.reindex blockIndexEquiv blockIndexEquiv
    (SUN.AdjointStabilizer.vacuum (I := Fin 3) (J := Fin 2) 2 (-3))

theorem vev_eq : vev = Matrix.diagonal ![2, 2, 2, -3, -3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem traceless : Matrix.trace vev = 0 := by
  rw [vev_eq, Matrix.trace_diagonal]
  norm_num [Fin.sum_univ_succ]

def subgroup : Subgroup TargetGroup := SUN.AdjointStabilizer.subgroup vev

theorem split_mem_iff (g : TargetGroup) : g ∈ subgroup ↔
    split g ∈ SUN.AdjointStabilizer.subgroup
      (SUN.AdjointStabilizer.vacuum (I := Fin 3) (J := Fin 2) 2 (-3)) := by
  change g.val * vev = vev * g.val ↔ _
  rw [← (Matrix.reindexRingEquiv ℂ blockIndexEquiv.symm).injective.eq_iff]
  simp only [map_mul]
  have hv : (Matrix.reindexRingEquiv ℂ blockIndexEquiv.symm) vev =
      SUN.AdjointStabilizer.vacuum (I := Fin 3) (J := Fin 2) 2 (-3) := by
    ext i j
    simp [vev, Matrix.reindex_apply]
  rw [hv]
  rfl

theorem fixed_iff (g : TargetGroup) : g.val * vev * g⁻¹.val = vev ↔ g ∈ subgroup :=
  SUN.AdjointStabilizer.fixed_iff vev g

/-- The exact embedded group is S(U(3) x U(2)), with determinant constraint,
not the covering product without its finite kernel. -/
theorem classification (g : TargetGroup) : g ∈ subgroup ↔
    ∃ A : Matrix (Fin 3) (Fin 3) ℂ, ∃ B : Matrix (Fin 2) (Fin 2) ℂ,
      A ∈ Matrix.unitaryGroup (Fin 3) ℂ ∧ B ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
      A.det * B.det = 1 ∧ (split g).val = Matrix.fromBlocks A 0 0 B := by
  rw [split_mem_iff]
  exact SUN.AdjointStabilizer.classification 2 (-3) (by norm_num) (split g)

theorem mem_iff_cross_entries (g : TargetGroup) : g ∈ subgroup ↔
    ∀ (i : Fin 3) (j : Fin 2),
      g.val (i.castAdd 2) (j.natAdd 3) = 0 ∧
      g.val (j.natAdd 3) (i.castAdd 2) = 0 := by
  rw [split_mem_iff]
  change (split g).val * Matrix.diagonal _ = Matrix.diagonal _ * (split g).val ↔ _
  rw [DiagonalCentralizer.two_eigenvalue_iff _ 2 (-3) (by norm_num)]
  exact ⟨fun h i j => ⟨h.1 i j, h.2 j i⟩,
    fun h => ⟨fun i j => (h i j).1, fun j i => (h i j).2⟩⟩

theorem covering_mem (g : StandardSMGaugeTensor.GaugeGroup) :
    StandardModelEmbedding.hom g ∈ subgroup := by
  rw [mem_iff_cross_entries]
  exact hom_cross_entries g

theorem covering_fixed (g : StandardSMGaugeTensor.GaugeGroup) :
    (StandardModelEmbedding.hom g).val * vev * (StandardModelEmbedding.hom g)⁻¹.val = vev :=
  (fixed_iff _).mpr (covering_mem g)
end
end GUT.SU5.AdjointVEVStabilizer
