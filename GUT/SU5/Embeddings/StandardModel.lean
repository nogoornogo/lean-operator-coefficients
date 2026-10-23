import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Mathlib.LinearAlgebra.Matrix.Reindex
import TauCeti.Topology.Algebra.UnitaryGroup

open Physics

/-!
# The standard covering homomorphism into SU(5)

The color-first convention is `(A,B,z) |-> diag(z^(-2) A, z^3 B)`.
The exponents are integral hypercharges `6Y`. This is a covering-group
homomorphism, not an injective map of the covering product.
-/

set_option autoImplicit false

namespace GUT.SU5.StandardModelEmbedding

noncomputable section

open StandardSMGaugeTensor

abbrev TargetGroup := Matrix.specialUnitaryGroup (Fin 5) ℂ
abbrev BlockIndex := Fin 3 ⊕ Fin 2
abbrev blockIndexEquiv : BlockIndex ≃ Fin 5 := finSumFinEquiv

def colorBlock (g : GaugeGroup) : Matrix (Fin 3) (Fin 3) ℂ :=
  (↑(g.2.2 ^ (-2 : ℤ)) : ℂ) • (g.1 : Matrix (Fin 3) (Fin 3) ℂ)

def weakBlock (g : GaugeGroup) : Matrix (Fin 2) (Fin 2) ℂ :=
  (↑(g.2.2 ^ (3 : ℤ)) : ℂ) • (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)

def rawMatrix (g : GaugeGroup) : Matrix BlockIndex BlockIndex ℂ :=
  Matrix.fromBlocks (colorBlock g) 0 0 (weakBlock g)

theorem circle_smul_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (z : Circle) (A : Matrix n n ℂ) (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    (z : ℂ) • A ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  have hz : (z : ℂ) * star (z : ℂ) = 1 := by
    simpa only [Circle.coe_mul, Circle.coe_inv_eq_conj, Circle.coe_one,
      Complex.star_def] using
      congrArg (fun w : Circle => (w : ℂ)) (mul_inv_cancel z)
  rw [star_smul, smul_mul_smul_comm, hA, hz, one_smul]

theorem rawMatrix_unitary (g : GaugeGroup) :
    rawMatrix g ∈ Matrix.unitaryGroup BlockIndex ℂ := by
  have hc := circle_smul_unitary (g.2.2 ^ (-2 : ℤ)) _
    (Matrix.specialUnitaryGroup_le_unitaryGroup g.1.prop)
  have hw := circle_smul_unitary (g.2.2 ^ (3 : ℤ)) _
    (Matrix.specialUnitaryGroup_le_unitaryGroup g.2.1.prop)
  rw [Matrix.mem_unitaryGroup_iff] at hc hw ⊢
  simp only [Matrix.star_eq_conjTranspose] at hc hw ⊢
  change colorBlock g * (colorBlock g).conjTranspose = 1 at hc
  change weakBlock g * (weakBlock g).conjTranspose = 1 at hw
  simp only [rawMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, hc, hw, Matrix.fromBlocks_one]

theorem rawMatrix_det (g : GaugeGroup) : Matrix.det (rawMatrix g) = 1 := by
  have hc : Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := g.1.prop.2
  have hw : Matrix.det (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := g.2.1.prop.2
  rw [rawMatrix, Matrix.det_fromBlocks_zero₂₁]
  simp only [colorBlock, weakBlock, Matrix.det_smul, Fintype.card_fin,
    hc, hw, mul_one]
  have h : (g.2.2 ^ (-2 : ℤ)) ^ (3 : ℕ) * (g.2.2 ^ (3 : ℤ)) ^ (2 : ℕ) = 1 := by group
  simpa only [Circle.coe_mul, Circle.coe_pow, Circle.coe_one] using
    congrArg ((↑) : Circle → ℂ) h

def rawHom : GaugeGroup →* Matrix BlockIndex BlockIndex ℂ where
  toFun := rawMatrix
  map_one' := by simp [rawMatrix, colorBlock, weakBlock, Matrix.fromBlocks_one]
  map_mul' g h := by
    simp [rawMatrix, colorBlock, weakBlock, Matrix.fromBlocks_multiply,
      mul_pow, smul_smul, mul_comm]

def matrixHom : GaugeGroup →* Matrix (Fin 5) (Fin 5) ℂ :=
  (Matrix.reindexRingEquiv ℂ blockIndexEquiv).toMonoidHom.comp rawHom

theorem matrixHom_unitary (g : GaugeGroup) :
    matrixHom g ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.mp (rawMatrix_unitary g)
  change Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g) *
    star (Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g)) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  change (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (rawMatrix g) *
    (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (star (rawMatrix g)) = 1
  rw [← map_mul, h, map_one]

theorem matrixHom_det (g : GaugeGroup) : Matrix.det (matrixHom g) = 1 := by
  change Matrix.det (Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g)) = 1
  rw [Matrix.det_reindex_self, rawMatrix_det]

def hom : GaugeGroup →* TargetGroup where
  toFun g := ⟨matrixHom g, matrixHom_unitary g, matrixHom_det g⟩
  map_one' := Subtype.ext (map_one matrixHom)
  map_mul' g h := Subtype.ext (map_mul matrixHom g h)

theorem continuous_hom : Continuous hom := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : GaugeGroup =>
    Matrix.reindex blockIndexEquiv blockIndexEquiv (rawMatrix g))
  unfold rawMatrix colorBlock weakBlock
  fun_prop (disch := simp)

def continuousHom : GaugeGroup →ₜ* TargetGroup where
  toMonoidHom := hom
  continuous_toFun := continuous_hom

@[simp] theorem blockIndexEquiv_color (i : Fin 3) :
    blockIndexEquiv (Sum.inl i) = i.castAdd 2 := rfl

@[simp] theorem blockIndexEquiv_weak (i : Fin 2) :
    blockIndexEquiv (Sum.inr i) = i.natAdd 3 := rfl

theorem hom_color_entry (g : GaugeGroup) (i j : Fin 3) :
    (hom g : Matrix (Fin 5) (Fin 5) ℂ) (i.castAdd 2) (j.castAdd 2) =
      phase (-2) g * (g.1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by
  change rawMatrix g (blockIndexEquiv.symm (blockIndexEquiv (Sum.inl i)))
    (blockIndexEquiv.symm (blockIndexEquiv (Sum.inl j))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem hom_weak_entry (g : GaugeGroup) (i j : Fin 2) :
    (hom g : Matrix (Fin 5) (Fin 5) ℂ) (i.natAdd 3) (j.natAdd 3) =
      phase 3 g * (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  change rawMatrix g (blockIndexEquiv.symm (blockIndexEquiv (Sum.inr i)))
    (blockIndexEquiv.symm (blockIndexEquiv (Sum.inr j))) = _
  simp only [Equiv.symm_apply_apply]
  rfl

theorem hom_cross_entries (g : GaugeGroup) (i : Fin 3) (j : Fin 2) :
    (hom g : Matrix (Fin 5) (Fin 5) ℂ) (i.castAdd 2) (j.natAdd 3) = 0 ∧
      (hom g : Matrix (Fin 5) (Fin 5) ℂ) (j.natAdd 3) (i.castAdd 2) = 0 := by
  change rawMatrix g (blockIndexEquiv.symm (blockIndexEquiv (Sum.inl i)))
      (blockIndexEquiv.symm (blockIndexEquiv (Sum.inr j))) = 0 ∧
    rawMatrix g (blockIndexEquiv.symm (blockIndexEquiv (Sum.inr j)))
      (blockIndexEquiv.symm (blockIndexEquiv (Sum.inl i))) = 0
  simp only [Equiv.symm_apply_apply]
  exact ⟨rfl, rfl⟩

theorem hom_eq_one_iff_blocks (g : GaugeGroup) :
    hom g = 1 ↔ colorBlock g = 1 ∧ weakBlock g = 1 := by
  have hreindex : hom g = 1 ↔ rawMatrix g = 1 := by
    change (⟨matrixHom g, _⟩ : TargetGroup) = 1 ↔ _
    rw [Subtype.ext_iff]
    change (Matrix.reindexRingEquiv ℂ blockIndexEquiv) (rawMatrix g) = 1 ↔ _
    rw [← map_one (Matrix.reindexRingEquiv ℂ blockIndexEquiv),
      (Matrix.reindexRingEquiv ℂ blockIndexEquiv).injective.eq_iff]
  rw [hreindex]
  constructor
  · intro h
    constructor
    · simpa only [rawMatrix, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
        using congrArg Matrix.toBlocks₁₁ h
    · simpa only [rawMatrix, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂]
        using congrArg Matrix.toBlocks₂₂ h
  · rintro ⟨hc, hw⟩
    simp [rawMatrix, hc, hw, Matrix.fromBlocks_one]

end

end GUT.SU5.StandardModelEmbedding
