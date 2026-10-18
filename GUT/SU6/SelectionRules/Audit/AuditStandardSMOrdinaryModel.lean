import GUT.SU6.SelectionRules.Models.StandardSMContinuousTensor

open Math

/-! Persistent audit of the canonical-carrier adapter and the full-gauge
tensor benchmark inside the continuous Weyl mass model. -/

set_option autoImplicit false

namespace GUT.AuditStandardSMOrdinaryModel

noncomputable section

open StandardSMOrdinaryMass StandardSMContinuousTensor
open StandardSMCharacterTarget
open ConcreteSU6PhysicalTarget (uniformCharges)

theorem continuous_benchmark (H : Type*) [CommGroup H] :
    (continuousModel H).generations = 1 ∧ (continuousModel H).mass.form ≠ 0 ∧
      Module.finrank ℂ (continuousModel H).mass.radical.toSubmodule = 15 ∧
      PhysicalWeylZeroModeSupport.lightSpectrum (continuousModel H).toPhysical =
        exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0 ∧
      qque H ≠ 0 ∧ duql H ≠ 0 ∧
      (∀ g x, qque H (qqueRho H g x) = qque H x) ∧
      (∀ g x, duql H (duqlRho H g x) = duql H x) :=
  ⟨rfl, continuous_mass_nonzero H, continuous_radical_finrank H,
    continuous_lightSpectrum H, qque_nonzero H, duql_nonzero H,
    qque_invariant H, duql_invariant H⟩

example : (continuousModel (Multiplicative (ZMod 2))).mass.form ≠ 0 :=
  continuous_mass_nonzero _

example : Module.finrank ℂ (continuousModel Unit).mass.radical.toSubmodule = 15 :=
  continuous_radical_finrank _

theorem zero_mass_not_fifteen :
    Module.finrank ℂ (InvariantWeylMass.SymmetricMass.zero
      (StandardWeylMassSource.ordinaryFields (ConcreteWeylBenchmark.matter Unit)).rho).radical.toSubmodule =
      27 := by
  rw [InvariantWeylMass.SymmetricMass.radical_zero]
  simpa using (ConcreteWeylBenchmark.fields_finrank (H := Unit))

#print axioms AbelianCharacterEquivalence.ofCharacter
#print axioms ContinuousRepresentationTransport.continuous_conjugate
#print axioms RepresentationConjugation.sealEquiv
#print axioms RepresentationConjugation.restriction_of_eq
#print axioms SplitRepresentationProjection.Split.pullback_invariant
#print axioms SplitRepresentationProjection.Split.certificate
#print axioms EquivariantWeylMassTransport.restrictTo
#print axioms EquivariantWeylMassTransport.certificate
#print axioms EquivariantWeylMassTransport.restrictToRadicalEquiv
#print axioms StandardSMOrdinaryFields.character_eq
#print axioms StandardSMOrdinaryFields.physicalEquiv
#print axioms StandardSMOrdinaryFields.su6Equiv
#print axioms StandardSMOrdinaryFields.su6_jointlyContinuous
#print axioms StandardSMOrdinaryFields.physical_restriction
#print axioms StandardSMOrdinaryFields.gauge_restriction
#print axioms StandardSMOrdinaryMass.mass_form_eq
#print axioms StandardSMOrdinaryMass.fullMass_form_eq
#print axioms StandardSMOrdinaryMass.fullMass
#print axioms StandardSMOrdinaryMass.uvGaugeEquiv
#print axioms StandardSMOrdinaryMass.continuous_mass_heq
#print axioms StandardSMOrdinaryMass.radicalEquiv
#print axioms StandardSMOrdinaryMass.physicalLightEquiv
#print axioms StandardSMOrdinaryMass.light_character
#print axioms StandardSMOrdinaryMass.radical_character
#print axioms StandardSMOrdinaryMass.lightSpectrum
#print axioms StandardSMOrdinaryMass.continuous_lightSpectrum
#print axioms StandardSMContinuousTensor.physical_restriction
#print axioms StandardSMContinuousTensor.physicalEquiv_eq
#print axioms StandardSMContinuousTensor.physicalFullEquiv
#print axioms StandardSMContinuousTensor.uvEquiv
#print axioms StandardSMContinuousTensor.qque_form_eq
#print axioms StandardSMContinuousTensor.duql_form_eq
#print axioms StandardSMContinuousTensor.qque_witness
#print axioms StandardSMContinuousTensor.duql_witness
#print axioms StandardSMContinuousTensor.qque_invariant
#print axioms StandardSMContinuousTensor.duql_invariant
#print axioms continuous_benchmark
#print axioms zero_mass_not_fifteen

end

end GUT.AuditStandardSMOrdinaryModel
