import GUT.SU6.SelectionRules.Models.WeylExchangeCandidate
import Math.LinearAlgebra.Matrix.DiagonalWeylStabilizer

/-! A compensated scalar-copy candidate. Its vacuum gate passes, but the
specified standard color transformation does not preserve the paired vacuum. -/
namespace GUT.PairedAdjointCandidate
set_option autoImplicit false
noncomputable section
open Matrix WeylMatrix WeylExchangeCandidate
abbrev SU6 := Matrix.specialUnitaryGroup (Fin 6) ℂ
abbrev Matrix6 := Matrix (Fin 6) (Fin 6) ℂ

def conjugate (g : SU6) (x : Matrix6) : Matrix6 :=
  (g : Matrix6) * x * ((g⁻¹ : SU6) : Matrix6)

theorem conjugate_mul (g h : SU6) (x : Matrix6) :
    conjugate (g * h) x = conjugate g (conjugate h x) := by
  unfold conjugate
  rw [_root_.mul_inv_rev]
  change ((g : Matrix6) * (h : Matrix6)) * x *
    (((h⁻¹ : SU6) : Matrix6) * ((g⁻¹ : SU6) : Matrix6)) = _
  noncomm_ring

theorem conjugate_one (x : Matrix6) : conjugate 1 x = x := by
  simp [conjugate]

def transform (x : Matrix6 × Matrix6) : Matrix6 × Matrix6 :=
  (conjugate signedSwap36SU x.2, conjugate signedSwap36SU x.1)

def pairedVacuum : Matrix6 × Matrix6 :=
  (vacuum, conjugate signedSwap36SU vacuum)

theorem fourth_power (x : Matrix6 × Matrix6) :
    transform (transform (transform (transform x))) = x := by
  have hw : signedSwap36SU * (signedSwap36SU *
      (signedSwap36SU * signedSwap36SU)) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using generator_SU_fourth_power
  ext i j <;>
    simp only [transform, ← conjugate_mul, hw, conjugate_one]

theorem pairedVacuum_fixed : transform pairedVacuum = pairedVacuum := by
  have htwice : conjugate signedSwap36SU (conjugate signedSwap36SU vacuum) = vacuum := by
    unfold conjugate vacuum
    rw [signedSwap36SU_conj_diagonal, signedSwap36SU_conj_diagonal]
    congr 1
    funext i
    simp [Function.comp_apply, swap36]
  exact Prod.ext htwice rfl

def colorPermutation : Equiv.Perm (Fin 6) := Equiv.swap 0 2

def colorPhases (i : Fin 6) : Circle := if i = 0 then -1 else 1

def colorMatrix : Matrix6 :=
  Math.DiagonalWeylStabilizer.representative colorPermutation colorPhases

theorem colorMatrix_specialUnitary : colorMatrix ∈ Matrix.specialUnitaryGroup (Fin 6) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    have he := Math.DiagonalWeylStabilizer.representative_conjugate
      colorPermutation colorPhases (fun _ => (1 : ℂ))
    simpa [colorMatrix, Function.comp_def] using he
  · unfold colorMatrix Math.DiagonalWeylStabilizer.representative
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation]
    norm_num [Fin.prod_univ_six, colorPhases, colorPermutation, Equiv.Perm.sign_swap]

def colorElement : SU6 := ⟨colorMatrix, colorMatrix_specialUnitary⟩

/-- Rows outside the three color coordinates are those of the identity. -/
theorem color_tail_rows (i j : Fin 6) (hi : 3 ≤ i.val) :
    colorMatrix i j = (1 : Matrix6) i j := by
  have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
  have h2 : i ≠ 2 := by intro h; subst i; norm_num at hi
  simp [colorMatrix, Math.DiagonalWeylStabilizer.representative,
    Matrix.diagonal_mul, colorPhases, colorPermutation,
    Equiv.Perm.permMatrix, Equiv.swap_apply_of_ne_of_ne h0 h2, h0, Matrix.one_apply]

theorem color_fixes_first : conjugate colorElement vacuum = vacuum := by
  change colorMatrix * vacuum * star colorMatrix = vacuum
  rw [colorMatrix, vacuum, Math.DiagonalWeylStabilizer.representative_conjugate]
  congr 1
  funext i
  fin_cases i <;> norm_num [Function.comp_apply, vacuumCoords, colorPermutation,
    Equiv.swap_apply_def, i6]

theorem color_does_not_fix_second :
    conjugate colorElement (conjugate signedSwap36SU vacuum) ≠
      conjugate signedSwap36SU vacuum := by
  unfold conjugate vacuum
  rw [signedSwap36SU_conj_diagonal]
  change colorMatrix * Matrix.diagonal (vacuumCoords ∘ swap36) * star colorMatrix ≠ _
  rw [colorMatrix, Math.DiagonalWeylStabilizer.representative_conjugate]
  intro he
  have hd := congrArg (fun m : Matrix6 => m 0 0) he
  norm_num [Function.comp_apply, colorPermutation, swap36, vacuumCoords,
    Equiv.swap_apply_def, i3, i6] at hd
theorem color_does_not_fix_pair :
    (conjugate colorElement pairedVacuum.1, conjugate colorElement pairedVacuum.2) ≠
      pairedVacuum := by
  intro he
  exact color_does_not_fix_second (congrArg Prod.snd he)

end
end GUT.PairedAdjointCandidate
