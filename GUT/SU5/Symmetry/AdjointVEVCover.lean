import GUT.SU5.Symmetry.AdjointVEVStabilizer
import GUT.SU5.Embeddings.StandardModelQuotient
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.CStarAlgebra.Basic

/-! The SM cover is onto the exact specified adjoint stabilizer. -/
namespace GUT.SU5.AdjointVEVStabilizer
set_option autoImplicit false
noncomputable section
open StandardModelEmbedding StandardSMGaugeTensor

def cover : GaugeGroup →* subgroup := hom.codRestrict subgroup covering_mem

@[simp] theorem cover_coe (g : GaugeGroup) : (cover g : TargetGroup) = hom g := rfl

/-- Normalize unitary blocks using a sixth root of their determinant. -/
theorem blocks_lift (A : Matrix (Fin 3) (Fin 3) ℂ)
    (B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Fin 3) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hd : A.det * B.det = 1) :
    ∃ g : GaugeGroup, colorBlock g = A ∧ weakBlock g = B := by
  let d : Circle := ⟨A.det, by
    simpa [Submonoid.unitSphere] using
      CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hA)⟩
  obtain ⟨z, hz⟩ := (Circle.isQuotientCoveringMap_npow 6).surjective d⁻¹
  have hc : (z : ℂ) ^ 6 * A.det = 1 := by
    change z ^ 6 = d⁻¹ at hz
    have h := congrArg (fun w : Circle => (w : ℂ))
      (show z ^ 6 * d = 1 by rw [hz]; simp)
    simpa only [Circle.coe_mul, Circle.coe_pow, Circle.coe_one] using h
  have hw : (↑(z ^ (-6 : ℤ)) : ℂ) * B.det = 1 := by
    have hi : (↑(z ^ (-6 : ℤ)) : ℂ) * (z : ℂ) ^ 6 = 1 := by
      simpa only [Circle.coe_mul, Circle.coe_pow, Circle.coe_one] using
        congrArg (fun w : Circle => (w : ℂ))
          (show z ^ (-6 : ℤ) * z ^ 6 = 1 by group)
    calc
      _ = ((↑(z ^ (-6 : ℤ)) : ℂ) * (z : ℂ) ^ 6) * (A.det * B.det) := by
        calc
          _ = (↑(z ^ (-6 : ℤ)) : ℂ) * ((↑z ^ 6 * A.det) * B.det) := by
            rw [hc, one_mul]
          _ = _ := by ring
      _ = 1 := by rw [hi, hd, mul_one]
  let C : Matrix.specialUnitaryGroup (Fin 3) ℂ :=
    ⟨(↑(z ^ (2 : ℤ)) : ℂ) • A, circle_smul_unitary _ A hA, by
      change Matrix.det ((↑(z ^ (2 : ℤ)) : ℂ) • A) = 1
      rw [Matrix.det_smul]
      have h : (z ^ (2 : ℤ)) ^ (3 : ℕ) = z ^ 6 := by group
      simpa only [Fintype.card_fin, ← Circle.coe_pow, h] using hc⟩
  let D : Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    ⟨(↑(z ^ (-3 : ℤ)) : ℂ) • B, circle_smul_unitary _ B hB, by
      change Matrix.det ((↑(z ^ (-3 : ℤ)) : ℂ) • B) = 1
      rw [Matrix.det_smul]
      have h : (z ^ (-3 : ℤ)) ^ (2 : ℕ) = z ^ (-6 : ℤ) := by group
      simpa only [Fintype.card_fin, ← Circle.coe_pow, h] using hw⟩
  refine ⟨(C, D, z), ?_, ?_⟩
  · change (↑(z ^ (-2 : ℤ)) : ℂ) • ((↑(z ^ (2 : ℤ)) : ℂ) • A) = A
    rw [smul_smul, ← Circle.coe_mul]
    have h : z ^ (-2 : ℤ) * z ^ (2 : ℤ) = 1 := by group
    rw [h, Circle.coe_one, one_smul]
  · change (↑(z ^ (3 : ℤ)) : ℂ) • ((↑(z ^ (-3 : ℤ)) : ℂ) • B) = B
    rw [smul_smul, ← Circle.coe_mul]
    have h : z ^ (3 : ℤ) * z ^ (-3 : ℤ) = 1 := by group
    rw [h, Circle.coe_one, one_smul]

theorem cover_surjective : Function.Surjective cover := by
  intro k
  obtain ⟨A, B, hA, hB, hd, hg⟩ := (classification k.val).mp k.property
  obtain ⟨g, hc, hw⟩ := blocks_lift A B hA hB hd
  refine ⟨g, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply (Matrix.reindexRingEquiv ℂ blockIndexEquiv.symm).injective
  change Matrix.reindex blockIndexEquiv.symm blockIndexEquiv.symm (hom g).val =
    (split k.val).val
  rw [hg]
  change Matrix.reindex blockIndexEquiv.symm blockIndexEquiv.symm
    (Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g)) = _
  simp [rawMatrix, hc, hw, Matrix.reindex_apply]

theorem image_eq_stabilizer : hom.range = subgroup := by
  ext k
  constructor
  · rintro ⟨g, rfl⟩
    exact covering_mem g
  · intro hk
    obtain ⟨g, hg⟩ := cover_surjective ⟨k, hk⟩
    exact ⟨g, congrArg Subtype.val hg⟩

theorem cover_kernel : cover.ker = hom.ker := by
  ext g
  change cover g = 1 ↔ hom g = 1
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The faithful global group, not the unquotiented covering product. -/
def quotientStabilizerEquiv : SMQuotient ≃* subgroup :=
  quotientImageEquiv.toMulEquiv.trans (MulEquiv.subgroupCongr image_eq_stabilizer)

@[simp] theorem quotientStabilizerEquiv_mk (g : GaugeGroup) :
    (quotientStabilizerEquiv (QuotientGroup.mk g) : TargetGroup) = hom g := rfl

def coverKernelCyclicEquiv : cover.ker ≃* Multiplicative (ZMod 6) :=
  (MulEquiv.subgroupCongr cover_kernel).trans kernelCyclicEquiv

theorem cover_kernel_card : Nat.card cover.ker = 6 := by
  rw [cover_kernel]
  exact kernel_card

theorem cover_kernel_le_center : cover.ker ≤ Subgroup.center GaugeGroup := by
  rw [cover_kernel]
  exact kernel_le_center

theorem cover_mem_kernel_iff (g : GaugeGroup) : g ∈ cover.ker ↔
    ∃ (z : Circle) (hz : z ^ 6 = 1), g = kernelElement z hz := by
  rw [cover_kernel]
  exact mem_ker_iff g

end
end GUT.SU5.AdjointVEVStabilizer
