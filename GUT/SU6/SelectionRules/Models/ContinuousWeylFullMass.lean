import GUT.SU6.SelectionRules.Models.ContinuousWeylMassTransport
import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylFullMass

/-! The nonzero fifteen-mode benchmark in the continuous-geometry model. -/

set_option autoImplicit false

namespace GUT.ContinuousWeylFullMass

noncomputable section

open ContinuousWeylModel StandardSMCharacterTarget ConcreteSU6PhysicalTarget

def model (H : Type*) [CommGroup H] : ContinuousWeylMassModel H :=
  ContinuousWeylMassTransport.ofStandard (ConcreteWeylFullMass.model H)

variable {H : Type*} [CommGroup H]

theorem mass_heq : HEq (model H).mass (ConcreteWeylFullMass.model H).mass :=
  ContinuousWeylMassTransport.mass_heq (ConcreteWeylFullMass.model H)

set_option maxHeartbeats 800000 in
theorem mass_nonzero : (model H).mass.form ≠ 0 :=
  (ContinuousWeylMassTransport.mass_nonzero_iff (ConcreteWeylFullMass.model H)).mpr
    (ConcreteWeylFullMass.fullMass_nonzero (H := H))

theorem radical_finrank : Module.finrank ℂ (model H).mass.radical.toSubmodule = 15 :=
  (ContinuousWeylMassTransport.radical_finrank (ConcreteWeylFullMass.model H)).trans
    (ConcreteWeylFullMass.fullMass_radical_finrank (H := H))

theorem lightSpectrum : PhysicalWeylZeroModeSupport.lightSpectrum (model H).toPhysical =
    exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0 :=
  (ContinuousWeylMassTransport.lightSpectrum (ConcreteWeylFullMass.model H)).trans
    (ConcreteWeylFullMass.model_lightSpectrum (H := H))

theorem exists_exact_sm_radical (H : Type*) [CommGroup H] :
    ∃ M : ContinuousWeylMassModel H, M.generations = 1 ∧ M.mass.form ≠ 0 ∧
      Module.finrank ℂ M.mass.radical.toSubmodule = 15 ∧
      PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical =
        exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ⟨model H, rfl, mass_nonzero, radical_finrank, lightSpectrum⟩

end

end GUT.ContinuousWeylFullMass
