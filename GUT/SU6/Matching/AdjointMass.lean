import GUT.SU6.Matching.ExteriorCurrents

open Math

/-! Explicit SU(6) background and all eleven broken complex root pairs.
The background and double-commutator kinetic normalization are model inputs. -/
set_option autoImplicit false
namespace GUT.SU6.AdjointMass
noncomputable section
open ExteriorCurrents
open scoped Matrix

def weight : Fin 6 → ℤ := ![2, 2, 2, -3, -3, 0]
def diagonal (v : ℝ) (i : Fin 6) : ℂ := (weight i : ℂ) * (v : ℂ)
def background (v : ℝ) : Matrix (Fin 6) (Fin 6) ℂ := Matrix.diagonal (diagonal v)

def massOperator (g v : ℝ) (X : Matrix (Fin 6) (Fin 6) ℂ) :=
  (g : ℂ) ^ 2 • DiagonalAdjointMass.operator (diagonal v) X

def massSquared (g v : ℝ) : Channel → ℝ
  | .inl _ => SU5.AdjointMass.massSquared g v
  | .inr i => (if i.val < 3 then 4 else 9) * g ^ 2 * v ^ 2

theorem background_trace (v : ℝ) : Matrix.trace (background v) = 0 := by
  simp [background, diagonal, weight, Matrix.trace, Fin.sum_univ_succ]
  ring

theorem background_hermitian (v : ℝ) : (background v)ᴴ = background v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [background, diagonal, weight, Matrix.conjTranspose_apply]

theorem upper_mass (g v : ℝ) (c : Channel) :
    massOperator g v (upper c) = (massSquared g v c : ℂ) • upper c := by
  rw [massOperator, upper, DiagonalAdjointMass.single_eigenvector, smul_smul]
  congr 1
  cases c with
  | inl aw =>
    rcases aw with ⟨a,w⟩
    fin_cases a <;> fin_cases w <;>
      simp [first, second, diagonal, weight, massSquared, SU5.AdjointMass.massSquared] <;> ring
  | inr i =>
    fin_cases i <;> simp [first, second, diagonal, weight, massSquared] <;> ring

theorem lower_mass (g v : ℝ) (c : Channel) :
    massOperator g v (lower c) = (massSquared g v c : ℂ) • lower c := by
  rw [massOperator, lower, DiagonalAdjointMass.single_eigenvector, smul_smul]
  congr 1
  cases c with
  | inl aw =>
    rcases aw with ⟨a,w⟩
    fin_cases a <;> fin_cases w <;>
      simp [first, second, diagonal, weight, massSquared, SU5.AdjointMass.massSquared] <;> ring
  | inr i =>
    fin_cases i <;> simp [first, second, diagonal, weight, massSquared] <;> ring

theorem massSquared_pos (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (c : Channel) :
    0 < massSquared g v c := by
  cases c with
  | inl aw => exact SU5.AdjointMass.massSquared_pos hg hv
  | inr i =>
    have hg2 := sq_pos_of_ne_zero hg
    have hv2 := sq_pos_of_ne_zero hv
    fin_cases i <;> simp only [massSquared] <;> norm_num <;> positivity

theorem massSquared_ne_zero (g v : ℝ) (hg : g ≠ 0) (hv : v ≠ 0) (c : Channel) :
    (massSquared g v c : ℂ) ≠ 0 := by
  exact_mod_cast ne_of_gt (massSquared_pos g v hg hv c)

theorem covers_broken_entries : ∀ i j : Fin 6, weight i ≠ weight j →
    ∃ c : Channel, (i = first c ∧ j = second c) ∨ (i = second c ∧ j = first c) := by
  decide

theorem equal_weight_entry_zero (g v : ℝ) (X : Matrix (Fin 6) (Fin 6) ℂ)
    (i j : Fin 6) (h : weight i = weight j) : massOperator g v X i j = 0 := by
  simp [massOperator, DiagonalAdjointMass.entry, diagonal, h]

end
end GUT.SU6.AdjointMass
