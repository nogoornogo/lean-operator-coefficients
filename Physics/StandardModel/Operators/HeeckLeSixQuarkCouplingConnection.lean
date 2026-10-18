import Physics.StandardModel.Operators.HeeckLeSixQuarkPairConnection
import Physics.StandardModel.Operators.HeeckLeSixQuarkQuotientConnection

/-! The five residual equations for the three remaining source-0 words and
the two quotient-kernel combinations. The statement is uniform in all five
coefficients and is derived directly from the original source recipes. -/
namespace GUT.HeeckLeSixQuarkCouplingConnection
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkReducedAction HeeckLeSixQuarkRecipe
open HeeckLeSixQuarkBlocks HeeckLeSixQuarkAssemblyBase HeeckLeSixQuarkPairCoordinates
open HeeckLeSixQuarkPairSolvers HeeckLeSixQuarkPairConnection
variable {K : Type*} [Field K]

private theorem entry0 (z : Fin 5 → K) :
    residual (couplingAssembly z) 0 = couplingForward z 0 := by
  rw [residual_apply]
  simp [even, odd, evenResidual, oddResidual, couplingAssembly, couplingColumn,
    combination, source1Assembly, source1Index,
    HeeckLeSixQuarkQuotient.kernelFirst, HeeckLeSixQuarkQuotient.kernelSecond,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    couplingForward, smul_eq_mul]
  all_goals ring

private theorem entry1 (z : Fin 5 → K) :
    residual (couplingAssembly z) 1 = couplingForward z 1 := by
  rw [residual_apply]
  simp [even, odd, evenResidual, oddResidual, couplingAssembly, couplingColumn,
    combination, source1Assembly, source1Index,
    HeeckLeSixQuarkQuotient.kernelFirst, HeeckLeSixQuarkQuotient.kernelSecond,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    couplingForward, smul_eq_mul]
  all_goals ring

private theorem entry2 (z : Fin 5 → K) :
    residual (couplingAssembly z) 2 = couplingForward z 2 := by
  rw [residual_apply]
  simp [even, odd, evenResidual, oddResidual, couplingAssembly, couplingColumn,
    combination, source1Assembly, source1Index,
    HeeckLeSixQuarkQuotient.kernelFirst, HeeckLeSixQuarkQuotient.kernelSecond,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    couplingForward, smul_eq_mul]
  all_goals ring

private theorem entry3 (z : Fin 5 → K) :
    residual (couplingAssembly z) 3 = couplingForward z 3 := by
  rw [residual_apply]
  simp [even, odd, evenResidual, oddResidual, couplingAssembly, couplingColumn,
    combination, source1Assembly, source1Index,
    HeeckLeSixQuarkQuotient.kernelFirst, HeeckLeSixQuarkQuotient.kernelSecond,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    couplingForward, smul_eq_mul]
  all_goals ring

private theorem entry4 (z : Fin 5 → K) :
    residual (couplingAssembly z) 4 = couplingForward z 4 := by
  rw [residual_apply]
  simp [even, odd, evenResidual, oddResidual, couplingAssembly, couplingColumn,
    combination, source1Assembly, source1Index,
    HeeckLeSixQuarkQuotient.kernelFirst, HeeckLeSixQuarkQuotient.kernelSecond,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    couplingForward, smul_eq_mul]
  all_goals ring

theorem residual_coupling (z : Fin 5 → K) :
    residual (couplingAssembly z) = couplingForward z := by
  ext i
  fin_cases i
  · exact entry0 z
  · exact entry1 z
  · exact entry2 z
  · exact entry3 z
  · exact entry4 z

end
end GUT.HeeckLeSixQuarkCouplingConnection
