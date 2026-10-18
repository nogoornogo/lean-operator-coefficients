import Math.RepresentationTheory.Multiplicity.CompactMultiplicityPresentation
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

namespace Math.NormalizedPresentationAudit
noncomputable section
open Representation NormalizedCharacterFamily

def repeated : Fin 2 → Representation ℂ Unit ℂ := fun _ => Representation.trivial ℂ Unit ℂ

theorem merged_coefficient (a : Fin 2 → ℤ) :
    coefficients repeated a (classOf repeated 0) = a 0 + a 1 := by
  classical
  simp [coefficients, Fin.sum_univ_two, classOf, repeated]

theorem signed_cancellation : coefficients repeated ![2, -2] (classOf repeated 0) = 0 := by
  rw [merged_coefficient]
  norm_num

theorem negative_coefficient : coefficients repeated ![2, -3] (classOf repeated 0) = -1 := by
  rw [merged_coefficient]
  norm_num

theorem one_class : Subsingleton (Index repeated) := by
  refine ⟨fun i j => Subtype.ext ?_⟩
  obtain ⟨i, hi⟩ := i.property
  obtain ⟨j, hj⟩ := j.property
  exact hi.symm.trans hj

theorem empty_family (S : Fin 0 → Representation ℂ Unit ℂ) : IsEmpty (Index S) := by
  refine ⟨fun i => ?_⟩
  obtain ⟨j, _⟩ := i.property
  exact Fin.elim0 j

end
end Math.NormalizedPresentationAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Normalized presentation imports upper layer {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.NormalizedCharacterFamily.inequivalent,
    ``Math.NormalizedCharacterFamily.continuous,
    ``Math.NormalizedCharacterFamily.character,
    ``Math.CompactCharacterPresentation.pi_character,
    ``Math.CompactCharacterPresentation.decomposition_character,
    ``Math.CompactCharacterPresentation.decomposition,
    ``Math.CompactCharacterPresentation.continuous,
    ``Math.CompactCharacterPresentation.inequivalent,
    ``Math.CompactCharacterPresentation.character,
    ``Math.CompactCharacterPresentation.difference,
    ``Math.CompactCharacterPresentation.coefficients_nonnegative,
    ``Math.CompactCharacterPresentation.coefficients_unique,
    ``Math.CompactCharacterPresentation.normalized,
    ``Math.CompactMultiplicityPresentation.index_character,
    ``Math.CompactMultiplicityPresentation.coefficient_hom_difference,
    ``Math.CompactMultiplicityPresentation.normalized,
    ``Math.NormalizedPresentationAudit.merged_coefficient,
    ``Math.NormalizedPresentationAudit.signed_cancellation,
    ``Math.NormalizedPresentationAudit.negative_coefficient,
    ``Math.NormalizedPresentationAudit.one_class,
    ``Math.NormalizedPresentationAudit.empty_family]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Normalized presentation: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Normalized presentation: {declarations.length} strict axiom checks passed"
