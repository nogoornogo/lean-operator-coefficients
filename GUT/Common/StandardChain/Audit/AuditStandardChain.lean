import Math.Audit.ImportOrigin
import GUT.SU5.SelectionRules.StandardChainBenchmark
import Physics.StandardModel.Spectrum.Audit.AuditFiniteChargeProfiles

open Math

/-! Common ambient-chain controls. The physical wrapper has an actual
continuous inhabitant, and finite charged examples satisfy the exact target.
This audit must not acquire an SU(6) source dependency. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Standard-chain audit imports SU(6): {mod}"

namespace GUT.AuditStandardChain

noncomputable section

open SU5 StandardModelEmbedding StandardChain StandardChainBenchmark
open AuditFiniteChargeProfiles FiniteAbelianChargeSectors

def orderThreeModel := model (cyclicLabels 3 1) (cyclicLabels 3 2)

theorem finite_charged_example :
    (cyclicLabels 3 1 : ChargeLabel (Multiplicative (ZMod 3))) ≠ 0 ∧
      Module.finrank ℂ orderThreeModel.mass.radical.toSubmodule = 15 ∧
      ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
        orderThreeModel.lightSpectrum :=
  ⟨order_three_character.1, radical_finrank _ _, orderThreeModel.selection_rule_obstruction⟩

def continuousNeutral {H : Type*} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] :=
  continuousModel (0 : ChargeLabel H) 0 continuous_const continuous_const

/-- A larger ambient group need not act faithfully on this benchmark.
The supplied SU(5) inclusion is still injective. -/
abbrev ExtraGroup := TargetGroup × Multiplicative (ZMod 2)

def extraInclusion : TargetGroup →* ExtraGroup := MonoidHom.inl _ _

def extraAction : Representation ℂ (ExtraGroup × Multiplicative (ZMod 3)) Space :=
  (rho (cyclicLabels 3 1) (cyclicLabels 3 2)).comp
    ((MonoidHom.fst _ _).prodMap (MonoidHom.id _))

def extraModel : Model extraInclusion extraAction where
  unitary := fun g => unitary (cyclicLabels 3 1) (cyclicLabels 3 2) (g.1.1, g.2)
  mass := InvariantWeylMass.SymmetricMass.zero _
  profile := family (cyclicLabels 3 1) (cyclicLabels 3 2)
  singlets := 0
  lightTarget := hasTarget (cyclicLabels 3 1) (cyclicLabels 3 2) _

theorem extra_inclusion_injective : Function.Injective extraInclusion := by
  intro a b he
  exact congrArg Prod.fst he

theorem extra_spectrum_eq : extraModel.lightSpectrum = orderThreeModel.lightSpectrum := rfl

theorem extra_result :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      extraModel.lightSpectrum := extraModel.selection_rule_obstruction

#print axioms CommutingUnitaryActions.charged_unitary
#print axioms CommutingUnitaryActions.charged_jointlyContinuous
#print axioms HilbertProductRepresentation.unitary
#print axioms HilbertProductRepresentation.character
#print axioms HilbertProductRepresentation.jointlyContinuous
#print axioms StandardChain.restrict_pullback
#print axioms StandardChain.pullback_comp
#print axioms StandardChain.pullback_unitary
#print axioms StandardChain.Model.ofSU5_spectrum
#print axioms StandardChain.Model.profiles_compatible
#print axioms StandardChain.Model.actual_signature_pair
#print axioms StandardChain.Model.selection_rule_obstruction
#print axioms StandardChain.ContinuousModel.pullback_continuous
#print axioms StandardChain.ContinuousModel.selection_rule_obstruction
#print axioms StandardChain.ScalarModel.toMassModel_form
#print axioms StandardChain.ScalarModel.toContinuousMassModel
#print axioms StandardChain.ScalarModel.ofMassModel_mass
#print axioms StandardChain.ScalarModel.selection_rule_obstruction
#print axioms TorusCharacter.eval_chiralDifference
#print axioms TorusMatterCharacter.charged_pair_character
#print axioms StandardChainBenchmark.character
#print axioms StandardChainBenchmark.hasTarget
#print axioms StandardChainBenchmark.model
#print axioms StandardChainBenchmark.nonvacuous
#print axioms StandardChainBenchmark.continuousModel
#print axioms StandardChainBenchmark.radical_finrank
#print axioms finite_charged_example
#print axioms continuousNeutral
#print axioms extra_inclusion_injective
#print axioms extra_spectrum_eq
#print axioms extra_result

end

end GUT.AuditStandardChain
