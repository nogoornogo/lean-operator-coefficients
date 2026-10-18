import Physics.StandardModel.Operators.HeeckLeSixQuarkAssemblyBase

/-! The ten displayed quotient equations are derived from the two literal
source vectors and the original short exchange words, for arbitrary source
coefficients. No evaluated matrix is an input. -/
namespace GUT.HeeckLeSixQuarkQuotientConnection
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkReducedAction HeeckLeSixQuarkRecipe
open HeeckLeSixQuarkBlocks HeeckLeSixQuarkAssemblyBase
variable {K : Type*} [Field K]

private theorem entry0 (b : Fin 12 → K) :
    top (source1Assembly b) 0 = HeeckLeSixQuarkQuotient.forward b 0 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry1 (b : Fin 12 → K) :
    top (source1Assembly b) 1 = HeeckLeSixQuarkQuotient.forward b 1 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry2 (b : Fin 12 → K) :
    top (source1Assembly b) 2 = HeeckLeSixQuarkQuotient.forward b 2 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry3 (b : Fin 12 → K) :
    top (source1Assembly b) 3 = HeeckLeSixQuarkQuotient.forward b 3 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry4 (b : Fin 12 → K) :
    top (source1Assembly b) 4 = HeeckLeSixQuarkQuotient.forward b 4 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry5 (b : Fin 12 → K) :
    top (source1Assembly b) 5 = HeeckLeSixQuarkQuotient.forward b 5 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry6 (b : Fin 12 → K) :
    top (source1Assembly b) 6 = HeeckLeSixQuarkQuotient.forward b 6 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry7 (b : Fin 12 → K) :
    top (source1Assembly b) 7 = HeeckLeSixQuarkQuotient.forward b 7 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry8 (b : Fin 12 → K) :
    top (source1Assembly b) 8 = HeeckLeSixQuarkQuotient.forward b 8 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

private theorem entry9 (b : Fin 12 → K) :
    top (source1Assembly b) 9 = HeeckLeSixQuarkQuotient.forward b 9 := by
  simp [top, source1Assembly, combination, source1Index,
    HeeckLeSixQuarkBlocks.orbit, selectedWord, selectedSeed, source, colorBase, spinBase,
    reducedAction_apply, colorReduced, spinReduced, Fin.sum_univ_succ,
    HeeckLeSixQuarkQuotient.forward, smul_eq_mul]
  all_goals ring

theorem top_source1 (b : Fin 12 → K) :
    top (source1Assembly b) = HeeckLeSixQuarkQuotient.forward b := by
  ext i
  fin_cases i
  · exact entry0 b
  · exact entry1 b
  · exact entry2 b
  · exact entry3 b
  · exact entry4 b
  · exact entry5 b
  · exact entry6 b
  · exact entry7 b
  · exact entry8 b
  · exact entry9 b

theorem top_assemble (v : Fin 25 → K) :
    top (assemble v) = HeeckLeSixQuarkQuotient.forward (select1 v) := by
  rw [assemble_split, map_add, top_source0, zero_add, top_source1]

end
end GUT.HeeckLeSixQuarkQuotientConnection
