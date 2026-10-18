import Math.Algebra.Lie.StandardSl3
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Tactic

/-!
# The standard solvable Borel subalgebra of `sl₃(ℂ)`

This file defines the upper-triangular Borel subalgebra of the concrete
`sl₃(ℂ)` model.  Its derived series is controlled by the strict upper
triangular ideal and then by the highest-root line.
-/

namespace Math
namespace StandardSl3

open LieAlgebra

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The upper-triangular trace-zero matrices inside `sl₃(ℂ)`. -/
def upperBorel : LieSubalgebra ℂ Algebra where
  carrier := {X | X.1 1 0 = 0 ∧ X.1 2 0 = 0 ∧ X.1 2 1 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX10, hX20, hX21⟩ ⟨hY10, hY20, hY21⟩
    simp [hX10, hX20, hX21, hY10, hY20, hY21]
  smul_mem' := by
    intro c X hX
    simp [hX.1, hX.2.1, hX.2.2]
  lie_mem' := by
    rintro X Y ⟨hX10, hX20, hX21⟩ ⟨hY10, hY20, hY21⟩
    constructor
    · change
        (X.1 * Y.1 - Y.1 * X.1) 1 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hY10, hX20, hY20]
    constructor
    · change
        (X.1 * Y.1 - Y.1 * X.1) 2 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX20, hX21, hY20, hY21,
        hX10, hY10]
    · change
        (X.1 * Y.1 - Y.1 * X.1) 2 1 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX20, hX21, hY20, hY21]

@[simp]
theorem mem_upperBorel (X : Algebra) :
    X ∈ upperBorel ↔ X.1 1 0 = 0 ∧ X.1 2 0 = 0 ∧ X.1 2 1 = 0 :=
  Iff.rfl

theorem H1_mem_upperBorel : H1 ∈ upperBorel := by
  simp [upperBorel, H1]

theorem H2_mem_upperBorel : H2 ∈ upperBorel := by
  simp [upperBorel, H2]

theorem E1_mem_upperBorel : E1 ∈ upperBorel := by
  simp [upperBorel, E1]

theorem E2_mem_upperBorel : E2 ∈ upperBorel := by
  simp [upperBorel, E2]

theorem E12_mem_upperBorel : E12 ∈ upperBorel := by
  simp [upperBorel, E12]

/-- The strict upper-triangular ideal of the Borel. -/
def strictUpperIdeal : LieIdeal ℂ upperBorel where
  carrier := {X | (X : Algebra).1 0 0 = 0 ∧ (X : Algebra).1 1 1 = 0 ∧
    (X : Algebra).1 2 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX0, hX1, hX2⟩ ⟨hY0, hY1, hY2⟩
    simp [hX0, hX1, hX2, hY0, hY1, hY2]
  smul_mem' := by
    intro c X hX
    simp [hX.1, hX.2.1, hX.2.2]
  lie_mem {X} {Y} hY := by
    rcases X.property with ⟨hX10, hX20, hX21⟩
    rcases Y.property with ⟨hY10, hY20, hY21⟩
    constructor
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 0 0) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hX20, hY10, hY20]
      ; ring
    constructor
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 1 1) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hX21, hY10, hY21]
      ; ring
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 2 2) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX20, hX21, hY20, hY21]
      ; ring

@[simp]
theorem mem_strictUpperIdeal (X : upperBorel) :
    X ∈ strictUpperIdeal ↔
      (X : Algebra).1 0 0 = 0 ∧ (X : Algebra).1 1 1 = 0 ∧
        (X : Algebra).1 2 2 = 0 :=
  Iff.rfl

/-- The highest-root line, characterized inside the Borel by the vanishing of
the diagonal and the two simple-root entries. -/
def highestRootIdeal : LieIdeal ℂ upperBorel where
  carrier := {X |
    (X : Algebra).1 0 0 = 0 ∧ (X : Algebra).1 1 1 = 0 ∧
    (X : Algebra).1 2 2 = 0 ∧ (X : Algebra).1 0 1 = 0 ∧
    (X : Algebra).1 1 2 = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX0, hX1, hX2, hX01, hX12⟩
      ⟨hY0, hY1, hY2, hY01, hY12⟩
    simp [hX0, hX1, hX2, hX01, hX12, hY0, hY1, hY2, hY01, hY12]
  smul_mem' := by
    intro c X hX
    simp [hX.1, hX.2.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2]
  lie_mem {X} {Y} hY := by
    rcases X.property with ⟨hX10, hX20, hX21⟩
    rcases Y.property with ⟨hY10, hY20, hY21⟩
    rcases hY with ⟨hY0, hY1, hY2, hY01, hY12⟩
    constructor
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 0 0) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hX20, hY10, hY20,
        hY0, hY01]
    constructor
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 1 1) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hX21, hY10, hY21,
        hY1, hY01, hY12]
    constructor
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 2 2) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX20, hX21, hY20, hY21,
        hY2, hY12]
    constructor
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 0 1) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX21,
        hY21, hY0, hY1, hY01]
    · change
        (((X : Algebra).1 * (Y : Algebra).1 -
          (Y : Algebra).1 * (X : Algebra).1) 1 2) = 0
      simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hY10, hY1, hY2, hY12]

@[simp]
theorem mem_highestRootIdeal (X : upperBorel) :
    X ∈ highestRootIdeal ↔
      (X : Algebra).1 0 0 = 0 ∧ (X : Algebra).1 1 1 = 0 ∧
      (X : Algebra).1 2 2 = 0 ∧ (X : Algebra).1 0 1 = 0 ∧
      (X : Algebra).1 1 2 = 0 :=
  Iff.rfl

theorem lie_mem_strictUpperIdeal (X Y : upperBorel) :
    ⁅X, Y⁆ ∈ strictUpperIdeal := by
  rcases X.property with ⟨hX10, hX20, hX21⟩
  rcases Y.property with ⟨hY10, hY20, hY21⟩
  constructor
  · change
      (((X : Algebra).1 * (Y : Algebra).1 -
        (Y : Algebra).1 * (X : Algebra).1) 0 0) = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hX20, hY10, hY20]
    ; ring
  constructor
  · change
      (((X : Algebra).1 * (Y : Algebra).1 -
        (Y : Algebra).1 * (X : Algebra).1) 1 1) = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hX10, hX21, hY10, hY21]
    ; ring
  · change
      (((X : Algebra).1 * (Y : Algebra).1 -
        (Y : Algebra).1 * (X : Algebra).1) 2 2) = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hX20, hX21, hY20, hY21]
    ; ring

theorem lie_mem_highestRootIdeal_of_mem_strictUpperIdeal
    {X Y : upperBorel} (hX : X ∈ strictUpperIdeal)
    (hY : Y ∈ strictUpperIdeal) :
    ⁅X, Y⁆ ∈ highestRootIdeal := by
  rcases hX with ⟨hX0, hX1, hX2⟩
  rcases hY with ⟨hY0, hY1, hY2⟩
  rcases X.property with ⟨hX10, hX20, hX21⟩
  rcases Y.property with ⟨hY10, hY20, hY21⟩
  have hDiag := lie_mem_strictUpperIdeal X Y
  refine ⟨hDiag.1, hDiag.2.1, hDiag.2.2, ?_, ?_⟩
  · change
      (((X : Algebra).1 * (Y : Algebra).1 -
        (Y : Algebra).1 * (X : Algebra).1) 0 1) = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hX0, hX1, hY0, hY1, hX21, hY21]
  · change
      (((X : Algebra).1 * (Y : Algebra).1 -
        (Y : Algebra).1 * (X : Algebra).1) 1 2) = 0
    simp [Matrix.mul_apply, Fin.sum_univ_three, hX1, hX2,
      hY1, hY2, hX10, hY10]

theorem lie_eq_zero_of_mem_highestRootIdeal
    {X Y : upperBorel} (hX : X ∈ highestRootIdeal)
    (hY : Y ∈ highestRootIdeal) :
    ⁅X, Y⁆ = 0 := by
  rcases hX with ⟨hX0, hX1, hX2, hX01, hX12⟩
  rcases hY with ⟨hY0, hY1, hY2, hY01, hY12⟩
  rcases X.property with ⟨hX10, hX20, hX21⟩
  rcases Y.property with ⟨hY10, hY20, hY21⟩
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  apply Subtype.ext
  change
    (X : Algebra).1 * (Y : Algebra).1 - (Y : Algebra).1 * (X : Algebra).1 = 0
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hX0, hX1, hX2, hX01, hX12,
      hY0, hY1, hY2, hY01, hY12, hX10, hX20, hX21, hY10, hY20, hY21]

theorem upperBorel_derivedSeries_one_le_strictUpperIdeal :
    derivedSeries ℂ upperBorel 1 ≤ strictUpperIdeal := by
  change ⁅(⊤ : LieIdeal ℂ upperBorel), (⊤ : LieIdeal ℂ upperBorel)⁆ ≤
    strictUpperIdeal
  rw [LieSubmodule.lie_le_iff]
  intro X hX Y hY
  exact lie_mem_strictUpperIdeal X Y

theorem lie_strictUpperIdeal_self_le_highestRootIdeal :
    ⁅strictUpperIdeal, strictUpperIdeal⁆ ≤ highestRootIdeal := by
  rw [LieSubmodule.lie_le_iff]
  intro X hX Y hY
  exact lie_mem_highestRootIdeal_of_mem_strictUpperIdeal hX hY

theorem lie_highestRootIdeal_self_eq_bot :
    ⁅highestRootIdeal, highestRootIdeal⁆ = ⊥ := by
  rw [eq_bot_iff, LieSubmodule.lie_le_iff]
  intro X hX Y hY
  rw [lie_eq_zero_of_mem_highestRootIdeal hX hY]
  exact LieSubmodule.zero_mem ⊥

private theorem upperBorel_derivedSeries_succ (n : ℕ) :
    derivedSeries ℂ upperBorel (n + 1) =
      ⁅derivedSeries ℂ upperBorel n, derivedSeries ℂ upperBorel n⁆ := by
  exact LieAlgebra.derivedSeriesOfIdeal_succ ℂ upperBorel
    (⊤ : LieIdeal ℂ upperBorel) n

theorem upperBorel_derivedSeries_two_le_highestRootIdeal :
    derivedSeries ℂ upperBorel 2 ≤ highestRootIdeal := by
  calc
    derivedSeries ℂ upperBorel 2 =
        ⁅derivedSeries ℂ upperBorel 1, derivedSeries ℂ upperBorel 1⁆ := by
          simp
    _ ≤ ⁅strictUpperIdeal, strictUpperIdeal⁆ :=
      LieSubmodule.mono_lie upperBorel_derivedSeries_one_le_strictUpperIdeal
        upperBorel_derivedSeries_one_le_strictUpperIdeal
    _ ≤ highestRootIdeal := lie_strictUpperIdeal_self_le_highestRootIdeal

theorem upperBorel_derivedSeries_three_eq_bot :
    derivedSeries ℂ upperBorel 3 = ⊥ := by
  apply le_antisymm
  · calc
      derivedSeries ℂ upperBorel 3 =
          ⁅derivedSeries ℂ upperBorel 2, derivedSeries ℂ upperBorel 2⁆ := by
            simp
      _ ≤ ⁅highestRootIdeal, highestRootIdeal⁆ :=
        LieSubmodule.mono_lie upperBorel_derivedSeries_two_le_highestRootIdeal
          upperBorel_derivedSeries_two_le_highestRootIdeal
      _ = ⊥ := lie_highestRootIdeal_self_eq_bot
  · exact bot_le

instance upperBorelIsSolvable : LieAlgebra.IsSolvable upperBorel :=
  LieAlgebra.IsSolvable.mk upperBorel_derivedSeries_three_eq_bot

end

end StandardSl3
end Math
