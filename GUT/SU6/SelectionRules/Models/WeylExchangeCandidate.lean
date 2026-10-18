import GUT.SU6.Characters.WeylMatrix

/-! Concrete generator test for a signed color/singlet exchange and a supplied
5+1 adjoint vacuum. This is a rejected candidate, not a full physical model. -/
namespace GUT.WeylExchangeCandidate
set_option autoImplicit false
noncomputable section
open Matrix WeylMatrix

/-- Explicit additional candidate choice: the 5+1 adjoint vacuum. -/
def vacuumCoords (i : Fin 6) : ℂ := if i = i6 then -5 else 1

def vacuum : Matrix (Fin 6) (Fin 6) ℂ := Matrix.diagonal vacuumCoords

theorem vacuum_trace_zero : Matrix.trace vacuum = 0 := by
  norm_num [vacuum, Matrix.trace, Fin.sum_univ_six, vacuumCoords, i6]

theorem generator_fourth_power : signedSwap36Matrix ^ 4 = 1 := by
  let d : Fin 6 → ℂ := fun i => sign36 i * sign36 (swap36 i)
  have hs : signedSwap36Matrix ^ 2 = Matrix.diagonal d := by
    rw [pow_two, signedSwap36Matrix]
    calc
      sign36Matrix * permutation36Matrix * (sign36Matrix * permutation36Matrix) =
          sign36Matrix * (permutation36Matrix * sign36Matrix * permutation36Matrix) := by
        noncomm_ring
      _ = sign36Matrix * Matrix.diagonal (sign36 ∘ swap36) := by
        rw [sign36Matrix, permutation36_conj_diagonal]
      _ = Matrix.diagonal d := by rw [sign36Matrix, Matrix.diagonal_mul_diagonal]; rfl
  have hd : ∀ i, d i * d i = 1 := by
    intro i
    change (sign36 i * sign36 (swap36 i)) * (sign36 i * sign36 (swap36 i)) = 1
    calc
      _ = (sign36 i * sign36 i) * (sign36 (swap36 i) * sign36 (swap36 i)) := by ring
      _ = 1 := by rw [sign36_sq, sign36_sq, one_mul]
  calc
    signedSwap36Matrix ^ 4 = (signedSwap36Matrix ^ 2) ^ 2 := (pow_mul signedSwap36Matrix 2 2)
    _ = Matrix.diagonal d * Matrix.diagonal d := by rw [hs, pow_two]
    _ = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases he : i = j
      · subst j; simp [hd]
      · simp [he]

theorem generator_SU_fourth_power : signedSwap36SU ^ 4 = 1 := by
  apply Subtype.ext
  change signedSwap36Matrix ^ 4 = 1
  exact generator_fourth_power

/-- The exchange preserves a diagonal adjoint vacuum iff the exchanged
coordinates have the same eigenvalue. -/
theorem diagonal_fixed_iff (d : Fin 6 → ℂ) :
    (signedSwap36SU : Matrix (Fin 6) (Fin 6) ℂ) * Matrix.diagonal d *
      ((signedSwap36SU⁻¹ : Matrix.specialUnitaryGroup (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ) =
      Matrix.diagonal d ↔ d i3 = d i6 := by
  rw [signedSwap36SU_conj_diagonal]
  constructor
  · intro he
    have hd := congrArg (fun m : Matrix (Fin 6) (Fin 6) ℂ => m i6 i6) he
    simpa [swap36] using hd
  · intro he
    congr 1
    funext i
    by_cases h3 : i = i3
    · subst i; simp [swap36, he]
    · by_cases h6 : i = i6
      · subst i; simp [swap36, he]
      · simp only [Function.comp_apply, swap36, Equiv.swap_apply_of_ne_of_ne h3 h6]

/-- Every nondegenerate 5+1 diagonal split fails this generator's vacuum gate. -/
theorem split_not_fixed (a b : ℂ) (hab : a ≠ b) :
    let d : Fin 6 → ℂ := fun i => if i = i6 then b else a
    (signedSwap36SU : Matrix (Fin 6) (Fin 6) ℂ) * Matrix.diagonal d *
      ((signedSwap36SU⁻¹ : Matrix.specialUnitaryGroup (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ) ≠
      Matrix.diagonal d := by
  dsimp only
  rw [ne_eq, diagonal_fixed_iff]
  simpa [i3, i6] using hab

/-- The existing signed Weyl representative fails the fixed-vacuum gate. -/
theorem vacuum_not_fixed :
    (signedSwap36SU : Matrix (Fin 6) (Fin 6) ℂ) * vacuum *
      ((signedSwap36SU⁻¹ : Matrix.specialUnitaryGroup (Fin 6) ℂ) : Matrix (Fin 6) (Fin 6) ℂ) ≠ vacuum := by
  intro he
  rw [vacuum, signedSwap36SU_conj_diagonal] at he
  have hd := congrArg (fun m : Matrix (Fin 6) (Fin 6) ℂ => m i6 i6) he
  norm_num [Matrix.diagonal_apply, Function.comp_apply, vacuumCoords,
    swap36, i3, i6] at hd

end
end GUT.WeylExchangeCandidate
