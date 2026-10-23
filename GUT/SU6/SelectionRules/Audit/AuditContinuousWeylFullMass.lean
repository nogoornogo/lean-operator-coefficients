import GUT.SU6.SelectionRules.Models.ContinuousWeylFullMass
import Lean.Util.CollectAxioms

open Physics

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

open Lean in
run_cmd do
  let ds := [
    ``Physics.SymmetricMassTransport.certificate,
    ``GUT.ContinuousWeylMassTransport.transport,
    ``GUT.ContinuousWeylMassTransport.ofStandard,
    ``GUT.ContinuousWeylMassTransport.mass_heq,
    ``GUT.ContinuousWeylMassTransport.mass_nonzero_iff,
    ``GUT.ContinuousWeylMassTransport.radicalEquiv,
    ``GUT.ContinuousWeylMassTransport.radical_finrank,
    ``GUT.ContinuousWeylMassTransport.radical_character,
    ``GUT.ContinuousWeylMassTransport.actualSpectrum,
    ``GUT.ContinuousWeylMassTransport.lightSpectrum]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mass transport {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Certified continuous mass transport: {ds.length} strict transitive checks passed"
