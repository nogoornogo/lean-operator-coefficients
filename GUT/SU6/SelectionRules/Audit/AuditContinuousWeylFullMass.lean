import GUT.SU6.SelectionRules.Models.ContinuousWeylFullMass

/-! Persistent audit: mass-preserving transport, full spectrum, non-vacuity. -/

set_option autoImplicit false

namespace GUT.AuditContinuousWeylFullMass

open ContinuousWeylModel StandardSMCharacterTarget ConcreteSU6PhysicalTarget

example : ∃ M : ContinuousWeylMassModel PUnit.{1}, M.generations = 1 ∧ M.mass.form ≠ 0 ∧
    Module.finrank ℂ M.mass.radical.toSubmodule = 15 ∧
    PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ContinuousWeylFullMass.exists_exact_sm_radical _

example : ∃ M : ContinuousWeylMassModel (Multiplicative (ZMod 2)),
    M.generations = 1 ∧ M.mass.form ≠ 0 ∧ Module.finrank ℂ M.mass.radical.toSubmodule = 15 ∧
    PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ContinuousWeylFullMass.exists_exact_sm_radical _

example : Nonempty (StandardModelLocalOperator.SupportedInvariantOperator
    (PhysicalWeylZeroModeSupport.lightSpectrum
      (ContinuousWeylFullMass.model (Multiplicative (ZMod 2))).toPhysical)) :=
  ⟨(ContinuousWeylFullMass.model _).supportedInvariantOperator (by change (0 : ℤ) < 1; norm_num)⟩

#print axioms StandardWeylFieldIdentification.fields_eq
#print axioms StandardWeylFieldIdentification.continuous_fields_eq
#print axioms ContinuousWeylMassTransport.ofStandard
#print axioms ContinuousWeylMassTransport.mass_heq
#print axioms ContinuousWeylMassTransport.radicalEquiv
#print axioms ContinuousWeylMassTransport.actualSpectrum
#print axioms ContinuousWeylMassTransport.lightSpectrum
#print axioms ContinuousWeylFullMass.mass_nonzero
#print axioms ContinuousWeylFullMass.radical_finrank
#print axioms ContinuousWeylFullMass.lightSpectrum
#print axioms ContinuousWeylFullMass.exists_exact_sm_radical

end GUT.AuditContinuousWeylFullMass
