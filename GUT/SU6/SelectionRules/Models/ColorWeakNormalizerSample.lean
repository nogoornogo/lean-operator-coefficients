import GUT.SU6.Characters.SignedWeylTransposition
import GUT.SU6.Branching.StandardSMGroup

open Physics

/-! A color/weak exchange fails to normalize the actual standard SM image.
The witness is independent of any vacuum or mass choice. -/
namespace GUT.ColorWeakNormalizerSample
set_option autoImplicit false
noncomputable section
open Matrix SignedWeylTransposition
abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℂ
abbrev SU6 := Matrix.specialUnitaryGroup (Fin 6) ℂ

def exchange : SU6 := signedTranspositionSU 0 3 (by decide)
def colorProbe : SU6 := signedTranspositionSU 0 2 (by decide)

def colorMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![0,0,-1], ![0,1,0], ![1,0,0]]

@[simp] theorem colorMatrix_apply (i j : Fin 3) :
    colorMatrix i j = (![![0,0,-1], ![0,1,0], ![1,0,0]] : Fin 3 → Fin 3 → ℂ) i j := rfl

theorem colorMatrix_SU : colorMatrix ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  constructor
  · change colorMatrix * colorMatrix.conjTranspose = 1
    ext i j
    change (∑ k : Fin 3, colorMatrix i k * star (colorMatrix j k)) =
      if i = j then 1 else 0
    fin_cases i <;> fin_cases j <;>
      norm_num [colorMatrix_apply, Fin.sum_univ_succ]
  · rw [Matrix.det_fin_three]
    norm_num [colorMatrix_apply]

def gaugeProbe : StandardSMGaugeTensor.GaugeGroup :=
  (⟨colorMatrix, colorMatrix_SU⟩, (1,1))

theorem probe_in_image : StandardSMGroup.hom gaugeProbe = colorProbe := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [StandardSMGroup.hom, StandardSMGroup.matrixHom,
      StandardSMGroup.rawHom, StandardSMGroup.rawMatrix,
      Matrix.reindex_apply, StandardSMGroup.blockIndexEquiv_symm,
      StandardSMGroup.colorBlock, StandardSMGroup.weakBlock,
      gaugeProbe, colorMatrix_apply, Matrix.smul_apply, Pi.smul_apply, colorProbe, signedMatrix, signMatrix, signAt,
      permutationMatrix, transposition, Matrix.diagonal_mul,
      Equiv.Perm.permMatrix, Equiv.swap_apply_def]

theorem image_cross_entry_zero (g : StandardSMGaugeTensor.GaugeGroup) :
    ((StandardSMGroup.hom g : SU6) : Matrix6) 3 2 = 0 := by
  simp [StandardSMGroup.hom, StandardSMGroup.matrixHom,
    StandardSMGroup.rawHom, StandardSMGroup.rawMatrix,
    Matrix.reindex_apply, StandardSMGroup.blockIndexEquiv_symm]

theorem conjugated_cross_entry :
    (((exchange * colorProbe * exchange⁻¹ : SU6) : Matrix6)) 3 2 = -1 := by
  change (signedMatrix 0 3 * signedMatrix 0 2 *
    ((exchange⁻¹ : SU6) : Matrix6)) 3 2 = -1
  rw [exchange, coe_signedTranspositionSU_inv]
  norm_num [signedMatrix, signedMatrixInv, signMatrix, signAt,
    permutationMatrix, transposition, Matrix.mul_apply,
    Fin.sum_univ_succ, Equiv.Perm.permMatrix, Equiv.swap_apply_def]

theorem conjugated_not_in_image :
    ¬ ∃ g : StandardSMGaugeTensor.GaugeGroup,
      StandardSMGroup.hom g = exchange * colorProbe * exchange⁻¹ := by
  rintro ⟨g, hg⟩
  have he := image_cross_entry_zero g
  rw [hg, conjugated_cross_entry] at he
  norm_num at he

/-- No automorphism of the SM covering group can implement this conjugation. -/
theorem no_cover_compensator :
    ¬ ∃ beta : StandardSMGaugeTensor.GaugeGroup →* StandardSMGaugeTensor.GaugeGroup,
      ∀ g, StandardSMGroup.hom (beta g) =
        exchange * StandardSMGroup.hom g * exchange⁻¹ := by
  rintro ⟨beta, hb⟩
  apply conjugated_not_in_image
  exact ⟨beta gaugeProbe, by simpa only [probe_in_image] using hb gaugeProbe⟩

end
end GUT.ColorWeakNormalizerSample
