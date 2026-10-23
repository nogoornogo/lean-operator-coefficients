import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylFullMass

open Physics

/-!
# Audit: exact SM radical on the original all-left-handed matter

The constructors require no eigenbasis, character, or light-spectrum premise.
The full actual spectrum is proved, not inferred from its dual difference.
Mass invariance is the declared physical torus times residual group; this
does not add a non-Abelian gauge-tensor or nonzero-amplitude assertion.
-/

set_option autoImplicit false

namespace GUT.AuditConcreteWeylFullMass

noncomputable section

open StandardWeylMassSource StandardSMCharacterTarget WeylZeroModeSupport
open ConcreteSU6PhysicalTarget

example : ∃ M : StandardWeylModel PUnit.{1},
    M.generations = 1 ∧ M.mass.form ≠ 0 ∧
      Module.finrank ℂ M.mass.radical.toSubmodule = 15 ∧
      lightSpectrum M = exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ConcreteWeylFullMass.exists_exact_sm_radical _

example : ∃ M : StandardWeylModel (Multiplicative (ZMod 2)),
    M.generations = 1 ∧ M.mass.form ≠ 0 ∧
      Module.finrank ℂ M.mass.radical.toSubmodule = 15 ∧
      lightSpectrum M = exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ConcreteWeylFullMass.exists_exact_sm_radical _

example : Nonempty (StandardModelLocalOperator.SupportedInvariantOperator
    (lightSpectrum (ConcreteWeylFullMass.model (Multiplicative (ZMod 2))))) :=
  ⟨supportedQque _ (by change (0 : ℤ) < 1; norm_num)⟩

#print axioms AbelianCharacterBasis.prescribedBasis
#print axioms AbelianCharacterBasis.prescribedBasis_action
#print axioms HyperbolicBasisMass.form_ne_zero
#print axioms HyperbolicBasisMass.mass
#print axioms HyperbolicBasisMass.radical_finrank
#print axioms HyperbolicBasisMass.radical_character
#print axioms ConcreteWeylFullMass.fields_character_sum
#print axioms ConcreteWeylFullMass.eigenbasis_action
#print axioms ConcreteWeylFullMass.fullMass_nonzero
#print axioms ConcreteWeylFullMass.fullMass_radical_finrank
#print axioms ConcreteWeylFullMass.fullMass_radical_character
#print axioms ConcreteWeylFullMass.fullMass_actualSpectrum
#print axioms ConcreteWeylFullMass.model_lightSpectrum
#print axioms ConcreteWeylFullMass.exists_exact_sm_radical

end

end GUT.AuditConcreteWeylFullMass
