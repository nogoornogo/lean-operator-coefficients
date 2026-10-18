import Physics.StandardModel.Operators.PairwisePositiveQque
import Math.RepresentationTheory.Characters.Audit.AuditCompactVirtualCharacter
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace GUT.PairwisePositiveQqueAudit
noncomputable section
open Representation SplitRepresentationProjection CompactVirtualCharacterAudit
open PairwisePositiveSpeciesIndex
open scoped TensorProduct

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance

def profiles (s : Fin 5) : Fin 2 → ℤ :=
  if s = 0 then ![1, 1] else if s = 1 then ![1, 0] else if s = 4 then ![0, 1] else 0

theorem pairwise_support : PairwisePositive profiles := by
  exact ⟨0, 1, by decide, by decide⟩

theorem no_three_way_support : ¬ SharedPositiveSpeciesIndex.SharedPositive profiles := by
  unfold SharedPositiveSpeciesIndex.SharedPositive profiles
  decide

def missingElectron (s : Fin 5) : Fin 2 → ℤ :=
  if s = 0 ∨ s = 1 then ![1, 0] else if s = 4 then ![0, 1] else 0

theorem missing_pair : ¬ PairwisePositive missingElectron := by
  unfold PairwisePositive missingElectron
  decide

abbrev qr := Split.fst (circleFamily 0) (circleFamily 1)
abbrev qs := Split.snd (circleFamily 0) (circleFamily 1)
abbrev ur := Split.ofEquiv (Representation.Equiv.refl (circleFamily 0))
abbrev es := Split.ofEquiv (Representation.Equiv.refl (circleFamily 1))

theorem distinct_quotients : IsEmpty (Representation.Equiv (circleFamily 0) (circleFamily 1)) :=
  circle_distinct 0 1 (by decide)

theorem model_exterior_nonzero : PairwiseQqueSpinorExterior.matched qr ur qs es ≠ 0 :=
  PairwiseQqueSpinorExterior.matched_nonzero qr ur qs es

theorem model_actual_alternation : QqueSpinorExterior.HasNonzeroAlternation
    (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] (ℂ × ℂ))
    (U := SMEpsilonTensor.Color ⊗[ℂ] Module.Dual ℂ ℂ) (E := ℂ ⊗[ℂ] Module.Dual ℂ ℂ)
    (QqueSpinorExterior.qField (a := (circleFamily 0).prod (circleFamily 1)))
    (QqueSpinorExterior.uField (b := circleFamily 0))
    (QqueSpinorExterior.eField (d := circleFamily 1)) :=
  PairwiseQqueSpinorExterior.exists_on_fields qr ur qs es _ _ _
    (Representation.Equiv.refl _) (Representation.Equiv.refl _) (Representation.Equiv.refl _)

theorem model_characters (z : Circle) :
    ((circleFamily 0).prod (circleFamily 1)).character z =
      CompactVirtualCharacter.character circleFamily (profiles 0) z ∧
    (circleFamily 0).character z = CompactVirtualCharacter.character circleFamily (profiles 1) z ∧
    (circleFamily 1).character z = CompactVirtualCharacter.character circleFamily (profiles 4) z := by
  refine ⟨?_, ?_, ?_⟩
  · change LinearMap.trace ℂ (ℂ × ℂ) ((circleFamily 0 z).prodMap (circleFamily 1 z)) = _
    rw [LinearMap.trace_prodMap']
    simp [CompactVirtualCharacter.character, profiles, Fin.sum_univ_two, Representation.character]
  · change (circleFamily 0).character z = CompactVirtualCharacter.character circleFamily ![1, 0] z
    simp [CompactVirtualCharacter.character, Fin.sum_univ_two]
  · change (circleFamily 1).character z = CompactVirtualCharacter.character circleFamily ![0, 1] z
    simp [CompactVirtualCharacter.character, Fin.sum_univ_two]

end
end GUT.PairwisePositiveQqueAudit

#check GUT.PairwisePositiveQque.exists_actual_alternation
#check GUT.PairwisePositiveQque.exists_actual_exterior

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Pairwise qque imports model layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.PairwisePositiveSpeciesIndex.PairwisePositive,
    ``GUT.PairwisePositiveSpeciesIndex.of_shared,
    ``GUT.PairwisePositiveSpeciesIndex.pairwise_quotients,
    ``GUT.PairwiseQqueSpinorExterior.internal,
    ``GUT.PairwiseQqueSpinorExterior.matched_diagonal,
    ``GUT.PairwiseQqueSpinorExterior.matched_nonzero,
    ``GUT.PairwiseQqueSpinorExterior.exists_on_fields,
    ``GUT.PairwisePositiveQque.exists_actual_alternation,
    ``GUT.PairwisePositiveQque.exists_actual_exterior,
    ``GUT.PairwisePositiveQqueAudit.pairwise_support,
    ``GUT.PairwisePositiveQqueAudit.no_three_way_support,
    ``GUT.PairwisePositiveQqueAudit.missing_pair,
    ``GUT.PairwisePositiveQqueAudit.distinct_quotients,
    ``GUT.PairwisePositiveQqueAudit.model_exterior_nonzero,
    ``GUT.PairwisePositiveQqueAudit.model_characters,
    ``GUT.PairwisePositiveQqueAudit.model_actual_alternation]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Pairwise qque: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Pairwise qque: {declarations.length} strict axiom checks passed"
