import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.TensorProduct.Pi

open Physics

/-! SM covering homomorphism into the PS covering product. No center quotient. -/
namespace GUT.PatiSalam.StandardModelEmbedding
set_option autoImplicit false
noncomputable section
open StandardSMGaugeTensor
abbrev Index := Fin 3 ⊕ Fin 1
abbrev PSGroup := Matrix.specialUnitaryGroup (Fin 4) ℂ ×
  Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev indexEquiv : Index ≃ Fin 4 := finSumFinEquiv

theorem index_color (a : Fin 3) : indexEquiv (Sum.inl a) = a.castSucc := rfl
theorem index_lepton (a : Fin 1) : indexEquiv (Sum.inr a) = 3 := by
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  rfl

def colorBlock (g : GaugeGroup) : Matrix (Fin 3) (Fin 3) ℂ :=
  (g.2.2 : ℂ) • (g.1 : Matrix (Fin 3) (Fin 3) ℂ)
def leptonBlock (g : GaugeGroup) : Matrix (Fin 1) (Fin 1) ℂ :=
  (↑(g.2.2 ^ (-3 : ℤ)) : ℂ) • 1
def rawMatrix (g : GaugeGroup) : Matrix Index Index ℂ :=
  Matrix.fromBlocks (colorBlock g) 0 0 (leptonBlock g)

theorem circle_smul_unitary {n : Type*} [Fintype n] [DecidableEq n]
    (z : Circle) (A : Matrix n n ℂ) (hA : A ∈ Matrix.unitaryGroup n ℂ) :
    (z : ℂ) • A ∈ Matrix.unitaryGroup n ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  have hz : (z : ℂ) * star (z : ℂ) = 1 := by
    simpa only [Circle.coe_mul, Circle.coe_inv_eq_conj, Circle.coe_one,
      Complex.star_def] using
      congrArg (fun w : Circle => (w : ℂ)) (mul_inv_cancel z)
  rw [star_smul, smul_mul_smul_comm, hA, hz, one_smul]

theorem rawMatrix_unitary (g : GaugeGroup) : rawMatrix g ∈ Matrix.unitaryGroup Index ℂ := by
  have hc := circle_smul_unitary g.2.2 _ (Matrix.specialUnitaryGroup_le_unitaryGroup g.1.prop)
  have hl := circle_smul_unitary (g.2.2 ^ (-3 : ℤ)) (1 : Matrix (Fin 1) (Fin 1) ℂ)
    (by simp)
  rw [Matrix.mem_unitaryGroup_iff] at hc hl ⊢
  simp only [Matrix.star_eq_conjTranspose] at hc hl ⊢
  change colorBlock g * (colorBlock g).conjTranspose = 1 at hc
  change leptonBlock g * (leptonBlock g).conjTranspose = 1 at hl
  simp only [rawMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    hc,hl,Matrix.fromBlocks_one]

theorem rawMatrix_det (g : GaugeGroup) : Matrix.det (rawMatrix g) = 1 := by
  have hc : Matrix.det (g.1 : Matrix (Fin 3) (Fin 3) ℂ) = 1 := g.1.prop.2
  rw [rawMatrix,Matrix.det_fromBlocks_zero₂₁]
  simp only [colorBlock,leptonBlock,Matrix.det_smul,Fintype.card_fin,
    hc,Matrix.det_one,mul_one,pow_one]
  have h : g.2.2 ^ (3:ℕ) * g.2.2 ^ (-3:ℤ) = 1 := by group
  simpa only [Circle.coe_mul,Circle.coe_pow,Circle.coe_one] using
    congrArg ((↑) : Circle → ℂ) h

def rawHom : GaugeGroup →* Matrix Index Index ℂ where
  toFun := rawMatrix
  map_one' := by simp [rawMatrix,colorBlock,leptonBlock,Matrix.fromBlocks_one]
  map_mul' g h := by
    simp [rawMatrix,colorBlock,leptonBlock,Matrix.fromBlocks_multiply,
      mul_pow,smul_smul,mul_comm]

def matrixHom : GaugeGroup →* Matrix (Fin 4) (Fin 4) ℂ :=
  (Matrix.reindexRingEquiv ℂ indexEquiv).toMonoidHom.comp rawHom

theorem matrixHom_unitary (g : GaugeGroup) : matrixHom g ∈ Matrix.unitaryGroup (Fin 4) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  have h := Matrix.mem_unitaryGroup_iff.mp (rawMatrix_unitary g)
  change Matrix.reindex indexEquiv indexEquiv (rawMatrix g) *
    star (Matrix.reindex indexEquiv indexEquiv (rawMatrix g)) = 1
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_reindex]
  change (Matrix.reindexRingEquiv ℂ indexEquiv) (rawMatrix g) *
    (Matrix.reindexRingEquiv ℂ indexEquiv) (star (rawMatrix g)) = 1
  rw [← map_mul,h,map_one]

theorem matrixHom_det (g : GaugeGroup) : Matrix.det (matrixHom g) = 1 := by
  change Matrix.det (Matrix.reindex indexEquiv indexEquiv (rawMatrix g)) = 1
  rw [Matrix.det_reindex_self,rawMatrix_det]

def su4Hom : GaugeGroup →* Matrix.specialUnitaryGroup (Fin 4) ℂ where
  toFun g := ⟨matrixHom g,matrixHom_unitary g,matrixHom_det g⟩
  map_one' := Subtype.ext (map_one matrixHom)
  map_mul' g h := Subtype.ext (map_mul matrixHom g h)

def rightMatrix (g : GaugeGroup) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal (fun i => if i=0 then (↑(g.2.2^(3:ℤ)):ℂ) else ↑(g.2.2^(-3:ℤ)))

theorem rightMatrix_unitary (g : GaugeGroup) : rightMatrix g ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rightMatrix,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.star_apply,
      ← Circle.coe_inv_eq_conj]

theorem rightMatrix_det (g : GaugeGroup) : Matrix.det (rightMatrix g) = 1 := by
  simp [rightMatrix,Matrix.det_diagonal,Fin.prod_univ_succ]

def rightHom : GaugeGroup →* Matrix.specialUnitaryGroup (Fin 2) ℂ where
  toFun g := ⟨rightMatrix g,rightMatrix_unitary g,rightMatrix_det g⟩
  map_one' := by apply Subtype.ext; simp [rightMatrix]
  map_mul' g h := by
    apply Subtype.ext
    change rightMatrix (g*h) = rightMatrix g * rightMatrix h
    simp only [rightMatrix,Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp [mul_pow, Circle.coe_mul,mul_comm]

def hom : GaugeGroup →* PSGroup :=
  su4Hom.prod (((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)).prod rightHom)

end
end GUT.PatiSalam.StandardModelEmbedding
