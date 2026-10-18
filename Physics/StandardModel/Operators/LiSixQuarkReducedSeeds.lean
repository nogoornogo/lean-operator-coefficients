import Physics.StandardModel.Operators.LiSixQuarkYoungImages

/-! The source diagrams populate the canonical Young image directions.
Only their scalar amplitudes need evaluation; all image identities are
uniform in the input array. -/
namespace GUT.LiSixQuarkReducedSeeds
noncomputable section
open LiSixQuarkLocalAction LiSixQuarkYoungOperators LiSixQuarkReducedAction
open LiSixQuarkYoungImages LiSixQuarkSeedRecipe
variable {K : Type*} [Field K] [CharZero K]

def reducedRaw (k : Fin 11) : Arr (K := K) := fun p q =>
  colorExtract (rawColor (LiSixQuarkRawSource.colorKind k)) p * spinExtract rawSpin q

theorem extraction_raw (k : Fin 11) : extraction (raw (K := K) k) = reducedRaw k := by
  change row extractSpin (column extractColor (fun p q =>
    rawColor (LiSixQuarkRawSource.colorKind k) p * rawSpin q)) = _
  rw [column_outer, row_outer]
  rfl

def reducedImage (k : Fin 11) (c : Arr (K := K)) : Arr (K := K) := match k with
  | 0 | 1 => profile0 c
  | 2 => profile2 c
  | 3 => (1/2 : K) • profile2 c
  | 4 | 5 => profile4 c
  | 6 => profile6 c
  | 7 | 8 => profile7 c
  | 9 => profile9 c
  | 10 => profile10 c

def reducedSeed (k : Fin 11) : Arr (K := K) := reducedImage k (reducedRaw k)

omit [CharZero K] in
private theorem young3 (t : Fin 4 → Module.End K (Arr (K := K))) (c : Arr (K := K)) :
    young t 3 c = (1/2 : K) • young t 2 c := by
  simp [young, down, primitive]

theorem image (k : Fin 11) (c : Arr (K := K)) :
    young reducedAction k c = reducedImage k c := by
  fin_cases k
  · exact image0 _
  · exact image0 _
  · exact image2 _
  · exact (young3 reducedAction c).trans (congrArg (fun x => (1/2 : K) • x) (image2 c))
  · exact image4 _
  · exact image4 _
  · exact image6 _
  · exact image7 _
  · exact image7 _
  · exact image9 _
  · exact image10 _

theorem extraction_projected (k : Fin 11) :
    extraction (projected (K := K) k) = reducedSeed k := by
  unfold projected
  rw [extraction_young, extraction_raw]
  exact image _ _

/-- The separating probe is half the trace of the 2-by-2 block. -/
theorem probe_eq_trace (c : Arr (K := ℂ)) :
    LiSixQuarkExtension.extraProbe c = (extraction c 0 0+extraction c 1 1)/2 := by
  simp [LiSixQuarkExtension.extraProbe, extraction, row, column,
    extractColor, extractSpin, colorExtract, spinExtract]
  ring

theorem printed_trace_zero (k : Fin 10) (c : Arr (K := ℂ)) :
    ((young reducedAction k.castSucc c) 0 0+
      (young reducedAction k.castSucc c) 1 1)/2 = 0 := by
  simp only [image]
  fin_cases k <;>
    simp [reducedImage, profile0, profile2, profile4, profile6, profile7, profile9]

theorem printed_probe_zero (k : Fin 10) :
    LiSixQuarkExtension.extraProbe (LiSixQuarkSemanticSeeds.seedCoordinates k.castSucc) = 0 := by
  rw [probe_eq_trace]
  change (extraction (projected k.castSucc) 0 0+
    extraction (projected k.castSucc) 1 1)/2 = 0
  unfold projected
  rw [extraction_young]
  exact printed_trace_zero k _

theorem extra_seed : LiSixQuarkSemanticSeeds.seedCoordinates 10 = LiSixQuarkExtension.extra := by
  apply extraction_injective
  change extraction (projected 10) = _
  rw [extraction_projected]
  ext p q
  fin_cases p <;> fin_cases q <;>
    norm_num [reducedSeed, reducedImage, profile10, reducedRaw, rawColor, rawSpin,
      LiSixQuarkRawSource.colorKind, colorExtract, spinExtract, extraction,
      row, column, extractColor, extractSpin, LiSixQuarkExtension.extra]

end
end GUT.LiSixQuarkReducedSeeds
