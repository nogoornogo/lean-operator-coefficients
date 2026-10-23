import Physics.StandardModel.Spectrum.Charges.LeptonTrialitySource
import Lean.Util.CollectAxioms

/-! Audit of the actual matter and mass construction. The joint gauge-weight
comparison with `LeptonTriality.spectrum` remains a separate endpoint. -/

set_option autoImplicit false

namespace Physics.LeptonTrialitySource.Audit

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

end Physics.LeptonTrialitySource.Audit

run_cmd do
  let declarations := [
    ``Physics.LeptonTrialitySource.generation_coefficients,
    ``Physics.LeptonTrialitySource.matter_coefficients,
    ``Physics.LeptonTrialitySource.modelEquiv,
    ``Physics.LeptonTrialitySource.model_continuous,
    ``Physics.LeptonTrialitySource.model_jointlyContinuous,
    ``Physics.LeptonTrialitySource.model_unitary,
    ``Physics.LeptonTrialitySource.model_finrank,
    ``Physics.LeptonTrialitySource.gauge_residual_commute,
    ``Physics.LeptonTrialitySource.mass,
    ``Physics.LeptonTrialitySource.radicalEquiv,
    ``Physics.LeptonTrialitySource.radical_finrank,
    ``Physics.LeptonTrialitySource.radical_character,
    ``Physics.LeptonTrialitySource.generation_character,
    ``Physics.LeptonTrialitySource.matter_character,
    ``Physics.LeptonTrialitySource.radical_character_formula,
    ``Physics.LeptonTrialitySource.radical_dual_character_formula,
    ``Physics.LeptonTrialitySource.generation_residual_basis,
    ``Physics.LeptonTrialitySource.matter_residual_basis,
    ``Physics.LeptonTrialitySource.exists_charged_zeroMode]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Triality source: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Triality source: {declarations.length} strict transitive axiom checks passed"
