import Physics.StandardModel.Spectrum.LeptonTrialitySource
import Lean.Util.CollectAxioms

/-! Audit of the actual matter and mass construction. The joint gauge-weight
comparison with `LeptonTriality.spectrum` remains a separate endpoint. -/

set_option autoImplicit false

namespace GUT.LeptonTrialitySource.Audit

example : Module.finrank ℂ HilbertMatter = 45 := model_finrank
example : Module.finrank ℂ mass.radical.toSubmodule = 45 := radical_finrank

example : Continuous (fun p : Group × HilbertMatter => unitaryModel p.1 p.2) :=
  model_jointlyContinuous

example (g : Group) (v w : HilbertMatter) :
    inner ℂ (unitaryModel g v) (unitaryModel g w) = inner ℂ v w :=
  model_unitary.inner_map_map g v w

example (g : Group) (v w : HilbertMatter) :
    mass.form (rho g v) (rho g w) = mass.form v w := mass.invariant g v w

example (i : MatterIndex) :
    ∃ v : mass.radical.toSubmodule, v ≠ 0 ∧ ∀ h : LeptonTriality.Residual,
      mass.radical.toRepresentation (1, h) v = (matterCharge i |>.toMul h : ℂ) • v :=
  exists_charged_zeroMode i

end GUT.LeptonTrialitySource.Audit

run_cmd do
  let declarations := [
    ``GUT.LeptonTrialitySource.generation_coefficients,
    ``GUT.LeptonTrialitySource.matter_coefficients,
    ``GUT.LeptonTrialitySource.modelEquiv,
    ``GUT.LeptonTrialitySource.model_continuous,
    ``GUT.LeptonTrialitySource.model_jointlyContinuous,
    ``GUT.LeptonTrialitySource.model_unitary,
    ``GUT.LeptonTrialitySource.model_finrank,
    ``GUT.LeptonTrialitySource.gauge_residual_commute,
    ``GUT.LeptonTrialitySource.mass,
    ``GUT.LeptonTrialitySource.radicalEquiv,
    ``GUT.LeptonTrialitySource.radical_finrank,
    ``GUT.LeptonTrialitySource.radical_character,
    ``GUT.LeptonTrialitySource.generation_character,
    ``GUT.LeptonTrialitySource.matter_character,
    ``GUT.LeptonTrialitySource.radical_character_formula,
    ``GUT.LeptonTrialitySource.radical_dual_character_formula,
    ``GUT.LeptonTrialitySource.generation_residual_basis,
    ``GUT.LeptonTrialitySource.matter_residual_basis,
    ``GUT.LeptonTrialitySource.exists_charged_zeroMode]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Triality source: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Triality source: {declarations.length} strict transitive axiom checks passed"
