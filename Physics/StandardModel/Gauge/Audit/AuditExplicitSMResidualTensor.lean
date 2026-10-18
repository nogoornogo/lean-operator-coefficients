import Physics.StandardModel.Gauge.CompactExplicitSMTensor
import Math.RepresentationTheory.FiniteFlavorControls
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

namespace GUT.ExplicitSMResidualTensorAudit
noncomputable section
open Representation ExplicitSMResidualTensor

/-- Canonical decomposed fields, not an assertion that every radical admits
the additional full-SM decomposition used by the source adapter. -/
theorem matched_fields {H V : Type*} [Group H] [AddCommGroup V] [Module ℂ V]
    [Nontrivial V] (r : Representation ℂ H V) :
    ∃ f : IntertwiningMap (fields r r r.dual r.dual)
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) ℂ), f ≠ 0 := by
  let s := SplitRepresentationProjection.Split.ofEquiv (Representation.Equiv.refl r)
  obtain ⟨p, hp⟩ := OrderedInvariantPairing.exists_ordered_coefficient s s s s
  exact ⟨qque r r r.dual r.dual p, qque_ne_zero r r r.dual r.dual p hp⟩

theorem s3_fields :
    ∃ f : IntertwiningMap
      (fields FiniteFlavorControls.s3 FiniteFlavorControls.s3
        FiniteFlavorControls.s3.dual FiniteFlavorControls.s3.dual)
      (Representation.trivial ℂ
        (StandardSMGaugeTensor.GaugeGroup × FiniteFlavorControls.S3) ℂ), f ≠ 0 :=
  matched_fields FiniteFlavorControls.s3

theorem a4_fields :
    ∃ f : IntertwiningMap
      (fields FiniteFlavorControls.a4 FiniteFlavorControls.a4
        FiniteFlavorControls.a4.dual FiniteFlavorControls.a4.dual)
      (Representation.trivial ℂ
        (StandardSMGaugeTensor.GaugeGroup × FiniteFlavorControls.A4) ℂ), f ≠ 0 :=
  matched_fields FiniteFlavorControls.a4

end
end GUT.ExplicitSMResidualTensorAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Explicit SM tensor imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.ExplicitSMResidualTensor.qque,
    ``GUT.ExplicitSMResidualTensor.qque_ne_zero,
    ``GUT.ExplicitSMResidualTensor.qque_tmul,
    ``GUT.ExplicitSMResidualTensor.qque_zero,
    ``GUT.ExplicitSMResidualTensor.qque_ne_zero_iff,
    ``GUT.ExplicitSMResidualTensor.exists_on_fields,
    ``GUT.CompactExplicitSMTensor.residual_agrees,
    ``GUT.CompactExplicitSMTensor.exists_qque,
    ``GUT.ExplicitSMResidualTensorAudit.matched_fields,
    ``GUT.ExplicitSMResidualTensorAudit.s3_fields,
    ``GUT.ExplicitSMResidualTensorAudit.a4_fields]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Explicit SM tensor: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Explicit SM tensor: layer and {declarations.length} strict axiom checks passed"
