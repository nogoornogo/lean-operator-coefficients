import Physics.StandardModel.Operators.FullLightRadicalQque
import Math.RepresentationTheory.Multiplicity.Audit.AuditEvaluationImage
import Lean.Util.CollectAxioms

open Math

/-! Exhaustiveness and model-boundary audit, without a positivity premise. -/
namespace GUT.FullLightSpeciesQqueAudit
noncomputable section
open Representation ProductFactorization MultiplicityEvaluationImage

/-- Even a reducible multiplicity has to be retained in full. -/
theorem all_scalar_copies (S : Subrepresentation (EvaluationImageAudit.ambient 2))
    (h : ∀ (f : MultiplicitySpace (EvaluationImageAudit.ambient 2)
      EvaluationImageAudit.scalar) (x : ℂ), f x ∈ S) : S = ⊤ := by
  have he := (image_le_iff (EvaluationImageAudit.ambient 2)
    EvaluationImageAudit.scalar S).mpr h
  rw [EvaluationImageAudit.image_eq_top] at he
  exact top_unique he

/-- The zero direction applies to the full model sector when a species is
absent; this check does not assume compactness or a topology on H. -/
theorem missing_up_forbidden {H K : Type*} [Group H]
    [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
    (tau : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) K)
    (hs : IsSemisimpleRepresentation (firstRestriction tau))
    [Subsingleton (MultiplicitySpace tau StandardSMGaugeTensor.upRight.dual)] :
    ∀ f : FullLightSpeciesQque.Sector tau, f = 0 := by
  apply (FullLightSpeciesQque.all_forbidden_iff tau hs).mpr
  intro k
  ext x
  exact Subsingleton.elim _ _

end
end GUT.FullLightSpeciesQqueAudit

run_cmd do
  let declarations := [
    ``Math.MultiplicityEvaluationImage.image_le_iff,
    ``GUT.FullLightSpeciesQque.quark_mem,
    ``GUT.FullLightSpeciesQque.up_mem,
    ``GUT.FullLightSpeciesQque.electron_mem,
    ``GUT.FullLightSpeciesQque.rightMultiplicityEquiv,
    ``GUT.FullLightSpeciesQque.fields,
    ``GUT.FullLightSpeciesQque.suppliedFieldsEquiv,
    ``GUT.FullLightSpeciesQque.equiv,
    ``GUT.FullLightSpeciesQque.nonzero_iff,
    ``GUT.FullLightSpeciesQque.all_forbidden_iff,
    ``GUT.FullLightSpeciesQque.supplied_alternation_iff,
    ``GUT.FullLightRadicalQque.sm_semisimple,
    ``GUT.FullLightRadicalQque.equiv,
    ``GUT.FullLightRadicalQque.nonzero_iff,
    ``GUT.FullLightRadicalQque.all_forbidden_iff,
    ``GUT.FullLightRadicalQque.nonzero_iff_of_jointlyContinuous,
    ``GUT.FullLightRadicalQque.all_forbidden_iff_of_jointlyContinuous,
    ``GUT.FullLightSpeciesQqueAudit.all_scalar_copies,
    ``GUT.FullLightSpeciesQqueAudit.missing_up_forbidden]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Full light species: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Full light species: {declarations.length} strict axiom checks passed"
