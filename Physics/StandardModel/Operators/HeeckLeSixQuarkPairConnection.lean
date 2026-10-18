import Physics.StandardModel.Operators.HeeckLeSixQuarkPairCoordinates

/-! The original paired words give the displayed even/odd block frames.
All coordinate identities below hold for arbitrary pair coefficients. -/
namespace GUT.HeeckLeSixQuarkPairConnection
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkReducedAction HeeckLeSixQuarkRecipe
open HeeckLeSixQuarkBlocks HeeckLeSixQuarkAssemblyBase HeeckLeSixQuarkPairCoordinates
open HeeckLeSixQuarkPairSolvers
variable {K : Type*} [Field K]

private theorem even_even_0 (x : Fin 5 → K) :
    even (evenAssembly x) 0 = evenForward x 0 := by
  simp [even, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, evenForward ]
  all_goals ring

private theorem even_even_1 (x : Fin 5 → K) :
    even (evenAssembly x) 1 = evenForward x 1 := by
  simp [even, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, evenForward ]
  all_goals ring

private theorem even_even_2 (x : Fin 5 → K) :
    even (evenAssembly x) 2 = evenForward x 2 := by
  simp [even, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, evenForward ]
  all_goals ring

private theorem even_even_3 (x : Fin 5 → K) :
    even (evenAssembly x) 3 = evenForward x 3 := by
  simp [even, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, evenForward ]
  all_goals ring

private theorem even_even_4 (x : Fin 5 → K) :
    even (evenAssembly x) 4 = evenForward x 4 := by
  simp [even, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, evenForward ]
  all_goals ring

private theorem even_even_5 (x : Fin 5 → K) :
    even (evenAssembly x) 5 = evenForward x 5 := by
  simp [even, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, evenForward ]
  all_goals ring

theorem even_even (x : Fin 5 → K) : even (evenAssembly x) = evenForward x := by
  ext i
  fin_cases i
  · exact even_even_0 x
  · exact even_even_1 x
  · exact even_even_2 x
  · exact even_even_3 x
  · exact even_even_4 x
  · exact even_even_5 x

private theorem odd_odd_0 (x : Fin 5 → K) :
    odd (oddAssembly x) 0 = oddForward x 0 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]
  all_goals ring

private theorem odd_odd_1 (x : Fin 5 → K) :
    odd (oddAssembly x) 1 = oddForward x 1 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]
  all_goals ring

private theorem odd_odd_2 (x : Fin 5 → K) :
    odd (oddAssembly x) 2 = oddForward x 2 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]

private theorem odd_odd_3 (x : Fin 5 → K) :
    odd (oddAssembly x) 3 = oddForward x 3 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]
  all_goals ring

private theorem odd_odd_4 (x : Fin 5 → K) :
    odd (oddAssembly x) 4 = oddForward x 4 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]
  all_goals ring

private theorem odd_odd_5 (x : Fin 5 → K) :
    odd (oddAssembly x) 5 = oddForward x 5 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]

private theorem odd_odd_6 (x : Fin 5 → K) :
    odd (oddAssembly x) 6 = oddForward x 6 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]
  all_goals ring

private theorem odd_odd_7 (x : Fin 5 → K) :
    odd (oddAssembly x) 7 = oddForward x 7 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]
  all_goals ring

private theorem odd_odd_8 (x : Fin 5 → K) :
    odd (oddAssembly x) 8 = oddForward x 8 := by
  simp [odd, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul, oddForward ]

theorem odd_odd (x : Fin 5 → K) : odd (oddAssembly x) = oddForward x := by
  ext i
  fin_cases i
  · exact odd_odd_0 x
  · exact odd_odd_1 x
  · exact odd_odd_2 x
  · exact odd_odd_3 x
  · exact odd_odd_4 x
  · exact odd_odd_5 x
  · exact odd_odd_6 x
  · exact odd_odd_7 x
  · exact odd_odd_8 x

private theorem odd_even_0 (x : Fin 5 → K) :
    odd (evenAssembly x) 0 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_1 (x : Fin 5 → K) :
    odd (evenAssembly x) 1 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_2 (x : Fin 5 → K) :
    odd (evenAssembly x) 2 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_3 (x : Fin 5 → K) :
    odd (evenAssembly x) 3 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_4 (x : Fin 5 → K) :
    odd (evenAssembly x) 4 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_5 (x : Fin 5 → K) :
    odd (evenAssembly x) 5 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_6 (x : Fin 5 → K) :
    odd (evenAssembly x) 6 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_7 (x : Fin 5 → K) :
    odd (evenAssembly x) 7 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem odd_even_8 (x : Fin 5 → K) :
    odd (evenAssembly x) 8 = 0 := by
  simp [odd, evenAssembly, combination, evenColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

theorem odd_even (x : Fin 5 → K) : odd (evenAssembly x) = 0 := by
  ext i
  fin_cases i
  · exact odd_even_0 x
  · exact odd_even_1 x
  · exact odd_even_2 x
  · exact odd_even_3 x
  · exact odd_even_4 x
  · exact odd_even_5 x
  · exact odd_even_6 x
  · exact odd_even_7 x
  · exact odd_even_8 x

private theorem even_odd_0 (x : Fin 5 → K) :
    even (oddAssembly x) 0 = 0 := by
  simp [even, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem even_odd_1 (x : Fin 5 → K) :
    even (oddAssembly x) 1 = 0 := by
  simp [even, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem even_odd_2 (x : Fin 5 → K) :
    even (oddAssembly x) 2 = 0 := by
  simp [even, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem even_odd_3 (x : Fin 5 → K) :
    even (oddAssembly x) 3 = 0 := by
  simp [even, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem even_odd_4 (x : Fin 5 → K) :
    even (oddAssembly x) 4 = 0 := by
  simp [even, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

private theorem even_odd_5 (x : Fin 5 → K) :
    even (oddAssembly x) 5 = 0 := by
  simp [even, oddAssembly, combination, oddColumn, pairLeft, pairRight,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ, smul_eq_mul ]

theorem even_odd (x : Fin 5 → K) : even (oddAssembly x) = 0 := by
  ext i
  fin_cases i
  · exact even_odd_0 x
  · exact even_odd_1 x
  · exact even_odd_2 x
  · exact even_odd_3 x
  · exact even_odd_4 x
  · exact even_odd_5 x

theorem residual_apply (c : Arr (K := K)) : residual c =
    ![evenResidual (even c),oddResidual (odd c) 0,oddResidual (odd c) 1,
      oddResidual (odd c) 2,oddResidual (odd c) 3] := rfl

theorem residual_even (x : Fin 5 → K) : residual (evenAssembly x) = 0 := by
  rw [residual_apply, even_even, odd_even, evenResidual_forward]
  ext i
  fin_cases i <;> simp [oddResidual]

theorem residual_odd (x : Fin 5 → K) : residual (oddAssembly x) = 0 := by
  rw [residual_apply, even_odd, odd_odd, oddResidual_forward]
  ext i
  fin_cases i <;> simp [evenResidual]

end
end GUT.HeeckLeSixQuarkPairConnection
