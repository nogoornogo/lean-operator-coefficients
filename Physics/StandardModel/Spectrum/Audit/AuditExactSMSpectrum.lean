import Physics.StandardModel.Operators.ExactSMSpectrumQque
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Exact-spectrum and adapter controls, not a new ambient GUT instance.
The final endpoint derives its targets, including all four weight equations. -/

namespace GUT.ExactSMSpectrumAudit
noncomputable section
open Representation ExactSMSpectrum StandardSMGaugeTensor

theorem model_has_spectrum (n s : ℕ) : HasSpectrum (action n s) n s :=
  ⟨Representation.Equiv.refl _⟩

theorem one_generation :
    Module.finrank ℂ (IntertwiningMap quark (action 1 0)) = 1 ∧
    Module.finrank ℂ (IntertwiningMap upRight.dual (action 1 0)) = 1 ∧
    Module.finrank ℂ (IntertwiningMap electronRight.dual (action 1 0)) = 1 :=
  exact_species_multiplicities (model_has_spectrum 1 0)

theorem three_generations_with_singlets :
    Module.finrank ℂ (IntertwiningMap quark (action 3 7)) = 3 ∧
    Module.finrank ℂ (IntertwiningMap upRight.dual (action 3 7)) = 3 ∧
    Module.finrank ℂ (IntertwiningMap electronRight.dual (action 3 7)) = 3 :=
  exact_species_multiplicities (model_has_spectrum 3 7)

theorem no_opposites (n s : ℕ) :
    Module.finrank ℂ (IntertwiningMap quark.dual (action n s)) = 0 ∧
    Module.finrank ℂ (IntertwiningMap upRight.dual.dual (action n s)) = 0 ∧
    Module.finrank ℂ (IntertwiningMap electronRight.dual.dual (action n s)) = 0 :=
  exact_opposite_multiplicities (model_has_spectrum n s)

theorem zero_generations (s : ℕ) :
    ¬ Nontrivial (IntertwiningMap quark (action 0 s)) := by
  intro hn
  let : Nontrivial (IntertwiningMap quark (action 0 s)) := hn
  have hz := (exact_species_multiplicities (model_has_spectrum 0 s)).1
  have hp := Module.finrank_pos (R := ℂ) (M := IntertwiningMap quark (action 0 s))
  omega

theorem dimension (n s : ℕ) : Module.finrank ℂ (Space n s) = 15 * n + s := by
  simp [Space, Generation, Quark, SMEpsilonTensor.Color, SMEpsilonTensor.Weak,
    Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_tensorProduct,
    mul_comm]

theorem monitored_and_opposite (n s : ℕ) (i : Fin 15) :
    ExactSMWeightMultiplicity.polynomial n s
        (SU5.TorusCharacter.weightCharacter (StandardSMCharacterTarget.smReducedWeight i)) = n ∧
    ExactSMWeightMultiplicity.polynomial n s
        (SU5.TorusCharacter.weightCharacter (StandardSMCharacterTarget.smReducedWeight i))⁻¹ = 0 :=
  ⟨ExactSMWeightMultiplicity.polynomial_positive n s i,
    ExactSMWeightMultiplicity.polynomial_negative n s i⟩

theorem singlets_do_not_supply_quarks (s : ℕ) :
    ExactSMWeightMultiplicity.polynomial 0 s
      (SU5.TorusCharacter.weightCharacter (StandardSMCharacterTarget.smReducedWeight 0)) = 0 := by
  simpa using ExactSMWeightMultiplicity.polynomial_positive 0 s 0

end
end GUT.ExactSMSpectrumAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Exact SM spectrum imports {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.ExactSMSpectrum.HasSpectrum,
    ``GUT.ExactSMSpectrum.intertwiner_eq_zero_of_hypercharge_ne,
    ``GUT.ExactSMSpectrum.exact_species_multiplicities,
    ``GUT.ExactSMSpectrum.exact_opposite_multiplicities,
    ``GUT.ExactSMResidualSpectrum.target,
    ``GUT.ExactSMResidualSpectrum.target_finrank,
    ``GUT.ExactSMResidualSpectrum.target_nontrivial,
    ``GUT.ExactSMResidualSpectrum.target_continuous,
    ``GUT.ExactSMResidualSpectrum.species_indices,
    ``GUT.ExactSMResidualSpectrum.has_species_target,
    ``GUT.ExactSMWeightMultiplicity.generation_trace,
    ``GUT.ExactSMWeightMultiplicity.coefficients_eq,
    ``GUT.ExactSMWeightMultiplicity.weight_finrank,
    ``GUT.ExactSMWeightMultiplicity.opposite_weight_finrank,
    ``GUT.MonitoredSMWeights.quark_zero,
    ``GUT.MonitoredSMWeights.quark_three,
    ``GUT.MonitoredSMWeights.up_eight,
    ``GUT.MonitoredSMWeights.electron_fourteen,
    ``GUT.ExactSMWeightEvaluation.evaluation,
    ``GUT.ExactSMWeightEvaluation.evaluation_injective,
    ``GUT.ExactSMWeightEvaluation.evaluationEquiv,
    ``GUT.ExactSMFourWeightTarget.index_eq_multiplicity,
    ``GUT.ExactSMFourWeightTarget.has_target,
    ``GUT.ExactSMSpectrumQque.exists_actual_alternation_of_four_weights,
    ``GUT.ExactSMSpectrumQque.exists_actual_exterior_of_four_weights,
    ``GUT.ExactSMSpectrumQque.exists_actual_alternation,
    ``GUT.ExactSMSpectrumQque.exists_actual_exterior,
    ``GUT.ExactSMSpectrumAudit.model_has_spectrum,
    ``GUT.ExactSMSpectrumAudit.one_generation,
    ``GUT.ExactSMSpectrumAudit.three_generations_with_singlets,
    ``GUT.ExactSMSpectrumAudit.no_opposites,
    ``GUT.ExactSMSpectrumAudit.zero_generations,
    ``GUT.ExactSMSpectrumAudit.dimension,
    ``GUT.ExactSMSpectrumAudit.monitored_and_opposite,
    ``GUT.ExactSMSpectrumAudit.singlets_do_not_supply_quarks]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Exact SM spectrum: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Exact SM spectrum: {declarations.length} strict axiom checks passed"
