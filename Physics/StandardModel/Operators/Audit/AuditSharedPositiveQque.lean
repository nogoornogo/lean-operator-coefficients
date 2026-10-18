import Physics.StandardModel.Operators.SharedPositiveQque
import Math.RepresentationTheory.Characters.Audit.AuditCompactVirtualCharacter
import Math.RepresentationTheory.Multiplicity.FiniteSpectrum
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace GUT.SharedPositiveQqueAudit
noncomputable section
open Representation ContinuousRepresentationScope CompactVirtualCharacter
open CompactVirtualCharacterAudit SharedPositiveSpeciesIndex

@[simp] private theorem four_ne_zero : (4 : Fin 5) ≠ 0 := by decide
@[simp] private theorem four_ne_one : (4 : Fin 5) ≠ 1 := by decide

def unequal (s : Fin 5) : Fin 2 → ℤ :=
  if s = 0 then ![1, -2] else if s = 1 then ![2, -2] else if s = 4 then ![3, -5] else 0

theorem shared : SharedPositive unequal := by
  exact ⟨0, by decide, by decide, by decide⟩

theorem totals :
    dimension (V := fun _ : Fin 2 => ℂ) (unequal 0) = -1 ∧
    dimension (V := fun _ : Fin 2 => ℂ) (unequal 1) = 0 ∧
    dimension (V := fun _ : Fin 2 => ℂ) (unequal 4) = -2 := by
  norm_num [dimension, unequal, Fin.sum_univ_two]

theorem characters_differ :
    CompactVirtualCharacter.character circleFamily (unequal 0) ≠
      CompactVirtualCharacter.character circleFamily (unequal 1) ∧
    CompactVirtualCharacter.character circleFamily (unequal 0) ≠
      CompactVirtualCharacter.character circleFamily (unequal 4) := by
  constructor <;> intro h
  all_goals
    have he := congrFun h 1
    norm_num [character_one, dimension, unequal, Fin.sum_univ_two] at he

theorem difference_realization (n m : ℕ) (z : Circle) :
    (FiniteSpectrum.copies n (circleFamily 0)).character z -
      (FiniteSpectrum.copies m (circleFamily 1)).character z =
        CompactVirtualCharacter.character circleFamily ![(n : ℤ), -(m : ℤ)] z := by
  simp [FiniteSpectrum.character_copies, CompactVirtualCharacter.character,
    Fin.sum_univ_two, sub_eq_add_neg]

theorem copies_continuous (n : ℕ) (k : Fin 2) :
    IsJointlyContinuous (FiniteSpectrum.copies n (circleFamily k)) := by
  change Continuous (fun p : Circle × (Fin n → ℂ) => fun i => circleFamily k p.1 (p.2 i))
  exact continuous_pi fun i => Continuous.comp (circle_continuous k)
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

theorem difference_split (n m : ℕ) (hn : 0 < n) :
    Nonempty (SplitRepresentationProjection.Split
      (FiniteSpectrum.copies n (circleFamily 0)) (circleFamily 0)) := by
  let : MeasurableSpace Circle := borel Circle
  let : BorelSpace Circle := ⟨rfl⟩
  apply CompactVirtualCharacter.exists_split circleFamily ![(n : ℤ), -(m : ℤ)]
    circle_continuous circle_distinct
    (FiniteSpectrum.copies n (circleFamily 0)) (FiniteSpectrum.copies m (circleFamily 1))
    (copies_continuous n 0) (copies_continuous m 1) (difference_realization n m) 0
  simpa using (Int.natCast_pos.mpr hn)

def disjoint (s : Fin 5) : Fin 2 → ℤ :=
  if s = 1 then ![0, 1] else if s = 0 ∨ s = 4 then ![1, 0] else 0

theorem no_shared : ¬ SharedPositive disjoint := by
  rintro ⟨i, hi⟩
  fin_cases i <;> norm_num [disjoint] at hi

theorem positive_totals_not_enough :
    (0 < dimension (V := fun _ : Fin 2 => ℂ) (disjoint 0) ∧
      0 < dimension (V := fun _ : Fin 2 => ℂ) (disjoint 1) ∧
      0 < dimension (V := fun _ : Fin 2 => ℂ) (disjoint 4)) ∧
      ¬ SharedPositive disjoint := by
  exact ⟨by norm_num [dimension, disjoint, Fin.sum_univ_two], no_shared⟩

end
end GUT.SharedPositiveQqueAudit

#check GUT.SharedPositiveQque.exists_actual_alternation
#check GUT.SharedPositiveQque.exists_actual_exterior

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Shared positive qque imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.SharedPositiveSpeciesIndex.SharedPositive,
    ``GUT.SharedPositiveSpeciesIndex.of_common_index,
    ``GUT.SharedPositiveSpeciesIndex.of_conjugations,
    ``GUT.SharedPositiveSpeciesIndex.common_quotient,
    ``GUT.SharedPositiveQque.exists_actual_alternation,
    ``GUT.SharedPositiveQque.exists_actual_exterior,
    ``GUT.SharedPositiveQqueAudit.shared,
    ``GUT.SharedPositiveQqueAudit.totals,
    ``GUT.SharedPositiveQqueAudit.characters_differ,
    ``GUT.SharedPositiveQqueAudit.difference_realization,
    ``GUT.SharedPositiveQqueAudit.copies_continuous,
    ``GUT.SharedPositiveQqueAudit.difference_split,
    ``GUT.SharedPositiveQqueAudit.no_shared,
    ``GUT.SharedPositiveQqueAudit.positive_totals_not_enough]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Shared positive qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Shared positive qque: {declarations.length} strict axiom checks passed"
