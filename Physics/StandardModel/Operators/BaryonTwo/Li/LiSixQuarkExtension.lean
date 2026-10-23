import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkPermutationCompleteness
import Mathlib.Tactic

/-! A local component invisible to down flavor spaces of dimension below four.
The explicit array is independently checked against the existing slot action.
It is an extension candidate, not one of Li's printed ten tableaux. -/
namespace Physics.LiSixQuarkExtension
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient Matrix

/-- Two color combinations: -C₀ + 2C₁ - C₃ and C₀ + 2C₂ - C₄. -/
abbrev extraColorFirst : Fin 5 → ℂ := ![-1,2,0,-1,0]
abbrev extraColorSecond : Fin 5 → ℂ := ![1,0,2,0,-1]
/-- The dual spin combinations X = S₀-S₁+S₂-S₃ and
Y = S₀+2S₁+S₂+2S₃. The added invariant pairs the two blocks. -/
abbrev extraSpinFirst : Fin 5 → ℂ := ![1,-1,1,-1,0]
abbrev extraSpinSecond : Fin 5 → ℂ := ![1,2,1,2,0]

/-- A⊗X + B⊗Y: the invariant pairing of the displayed two-dimensional
color and spin blocks. This replaces the unexplained 5-by-5 array. -/
def extra (p q : Fin 5) : ℂ :=
  extraColorFirst p * extraSpinFirst q + extraColorSecond p * extraSpinSecond q

def localSign (g : Fin 4) : ℂ := if g = 0 then -1 else 1

/-- Only two-dimensional block actions need inspection: up exchange is
(I,-I), the middle down exchange swaps both pairs, and the other two down
exchanges are dual reflections. -/
theorem extra_color_action (g : Fin 4) :
    (colorMatrix g *ᵥ extraColorFirst =
      (![extraColorFirst, -extraColorFirst, extraColorSecond, -extraColorFirst] :
        Fin 4 → Fin 5 → ℂ) g) ∧
    (colorMatrix g *ᵥ extraColorSecond =
      (![extraColorSecond, -extraColorFirst + extraColorSecond,
        extraColorFirst, -extraColorFirst + extraColorSecond] :
        Fin 4 → Fin 5 → ℂ) g) := by
  constructor <;> ext p <;> fin_cases g <;> fin_cases p <;>
    norm_num [Matrix.mulVec, dotProduct, colorMatrix, Fin.sum_univ_succ]

theorem extra_spin_action (g : Fin 4) :
    (spinMatrix g *ᵥ extraSpinFirst =
      (![-extraSpinFirst, -extraSpinFirst - extraSpinSecond,
        extraSpinSecond, -extraSpinFirst - extraSpinSecond] :
        Fin 4 → Fin 5 → ℂ) g) ∧
    (spinMatrix g *ᵥ extraSpinSecond =
      (![-extraSpinSecond, extraSpinSecond, extraSpinFirst, extraSpinSecond] :
        Fin 4 → Fin 5 → ℂ) g) := by
  constructor <;> ext p <;> fin_cases g <;> fin_cases p <;>
    norm_num [Matrix.mulVec, dotProduct, spinMatrix, Fin.sum_univ_succ]

/-- Tensor transport is a symbolic identity for arbitrary vectors. -/
theorem transform_outer (a b : Fin 5 → ℂ) (g : Fin 4) :
    transform (fun p q => a p * b q) g =
      fun p q => (colorMatrix g *ᵥ a) p * (spinMatrix g *ᵥ b) q := by
  ext p q
  simp only [transform, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem transform_add (a b : Fin 5 → Fin 5 → ℂ) (g : Fin 4) :
    transform (a + b) g = transform a g + transform b g := by
  ext p q
  simp [transform, mul_add, Finset.sum_add_distrib]

theorem extra_transform (g : Fin 4) :
    transform extra g = localSign g • extra := by
  change transform ((fun p q => extraColorFirst p * extraSpinFirst q) +
    (fun p q => extraColorSecond p * extraSpinSecond q)) g = _
  rw [transform_add, transform_outer, transform_outer,
    (extra_color_action g).1, (extra_color_action g).2,
    (extra_spin_action g).1, (extra_spin_action g).2]
  ext p q
  fin_cases g
  · change extraColorFirst p * (-extraSpinFirst q) +
      extraColorSecond p * (-extraSpinSecond q) =
      -1 * (extraColorFirst p * extraSpinFirst q + extraColorSecond p * extraSpinSecond q)
    ring
  · change (-extraColorFirst p) * (-extraSpinFirst q - extraSpinSecond q) +
      (-extraColorFirst p + extraColorSecond p) * extraSpinSecond q =
      1 * (extraColorFirst p * extraSpinFirst q + extraColorSecond p * extraSpinSecond q)
    ring
  · change extraColorSecond p * extraSpinSecond q + extraColorFirst p * extraSpinFirst q =
      1 * (extraColorFirst p * extraSpinFirst q + extraColorSecond p * extraSpinSecond q)
    ring
  · change (-extraColorFirst p) * (-extraSpinFirst q - extraSpinSecond q) +
      (-extraColorFirst p + extraColorSecond p) * extraSpinSecond q =
      1 * (extraColorFirst p * extraSpinFirst q + extraColorSecond p * extraSpinSecond q)
    ring

theorem extra_ne_zero : extra ≠ 0 := by
  intro h
  have he := congrFun (congrFun h 1) 0
  norm_num [extra] at he

def coefficient : Coefficient := reconstruct extra

theorem coefficient_invariant : IsInvariant coefficient := reconstruct_invariant _

theorem coefficient_coordinates : coordinates coefficient = extra := coordinates_reconstruct _

theorem coefficient_ne_zero : coefficient ≠ 0 := by
  intro h
  apply extra_ne_zero
  rw [← coefficient_coordinates, h]
  exact SixQuarkFlavorCoordinates.coordinateLinear.map_zero

theorem coefficient_exchange (g : Fin 4) :
    coefficient.domDomCongr (slotSwap g) = localSign g • coefficient := by
  change (reconstruct extra).domDomCongr (slotSwap g) = _
  rw [← reconstruct_transform, extra_transform]
  simp [coefficient, reconstruct, Finset.smul_sum, smul_smul]

/-- A separating dual character, normalized to read 1 on `extra`. -/
def extraProbe (c : Fin 5 → Fin 5 → ℂ) : ℂ :=
  (2*c 1 0 - c 1 1 + 2*c 1 2 - c 1 3 - c 1 4 +
    c 2 0 + c 2 1 + c 2 2 + c 2 3 - 2*c 2 4) / 24

theorem extraProbe_extra : extraProbe extra = 1 := by norm_num [extraProbe, extra]

theorem extraProbe_transform (c : Fin 5 → Fin 5 → ℂ) (g : Fin 4) :
    extraProbe (transform c g) = localSign g * extraProbe c := by
  fin_cases g <;>
    simp [extraProbe, transform, localSign, colorMatrix, spinMatrix,
      Fin.sum_univ_succ] <;> ring

def extraProbeLinear : (Fin 5 → Fin 5 → ℂ) →ₗ[ℂ] ℂ where
  toFun := extraProbe
  map_add' c d := by simp [extraProbe]; ring
  map_smul' z c := by simp [extraProbe, smul_eq_mul]; ring

theorem extraProbe_word (c : Fin 5 → Fin 5 → ℂ) (w : List (Fin 4))
    (h : extraProbe c = 0) :
    extraProbe (w.foldl (fun c g => transform c g) c) = 0 := by
  induction w generalizing c with
  | nil => exact h
  | cons g w ih =>
    apply ih
    rw [extraProbe_transform, h, mul_zero]

theorem extra_not_scalar_statistics : ¬ SatisfiesStatistics extra := by
  intro h
  have he := h 1 1 0
  norm_num [SixQuarkSpeciesQuotient.residual, transform, extra, colorMatrix, spinMatrix,
    Fin.sum_univ_succ] at he

end
end Physics.LiSixQuarkExtension
