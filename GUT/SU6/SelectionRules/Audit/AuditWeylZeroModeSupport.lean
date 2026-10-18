import GUT.SU6.SelectionRules.StandardBranch.WeylZeroModeSupport
import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylNonzeroMass

open Math

/-!
# Audit: actual radical support and a nonzero benchmark mass

The constructors below have no orbit-support or eigenvector hypotheses.
Finite residual groups are included without a continuity assumption on them.
Only the existing operator-signature selection rule is asserted, not a
nonzero Wilson coefficient or a full non-Abelian gauge tensor construction.
-/

set_option autoImplicit false

namespace GUT.AuditWeylZeroModeSupport

noncomputable section

open WeylZeroModeSupport StandardModelLocalOperator StandardSMCharacterTarget

example : Nonempty (SupportedInvariantOperator
    (lightSpectrum (ConcreteWeylBenchmark.model PUnit.{1}))) :=
  ⟨supportedQque _ (by change (0 : ℤ) < 1; norm_num)⟩

example : Nonempty (SupportedInvariantOperator
    (lightSpectrum (ConcreteWeylNonzeroMass.model (Multiplicative (ZMod 2))))) :=
  ⟨supportedDuql _ (by change (0 : ℤ) < 1; norm_num)⟩

example : ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
    (lightSpectrum (ConcreteWeylNonzeroMass.model (Multiplicative (ZMod 2)))) :=
  not_forbidsEverySupportedPhysicalDeltaBOneOperator _ (by change (0 : ℤ) < 1; norm_num)

example (i : Fin 15) :
    let M := ConcreteWeylNonzeroMass.model (Multiplicative (ZMod 2))
    ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom (smResolvedKey M.charges i) g • v :=
  all_sm_zeroModes _ (by change (0 : ℤ) < 1; norm_num) i

example : ∃ M : StandardWeylMassSource.StandardWeylModel (Multiplicative (ZMod 2)),
    M.generations = 1 ∧ M.mass.form ≠ 0 ∧
      Module.finrank ℂ M.mass.radical.toSubmodule = 26 :=
  ConcreteWeylNonzeroMass.exists_one_generation_nonzero_mass _

#print axioms AbelianActualSpectrum.eval_injective
#print axioms AbelianActualSpectrum.spectrum_eval
#print axioms AbelianActualSpectrum.spectrum_nonneg
#print axioms AbelianActualSpectrum.spectrum_eq_unitaryCharacterSpectrum
#print axioms AbelianActualSpectrum.exists_eigenvector_of_coeff_ne_zero
#print axioms AbelianActualSpectrum.exists_eigenvector_of_dual_coeff_pos
#print axioms lightSpectrum_chiralDifference
#print axioms all_sm_zeroModes
#print axioms all_conjugate_sm_zeroModes
#print axioms chargesSupported
#print axioms WeylZeroModeSupport.supportedQque
#print axioms WeylZeroModeSupport.supportedDuql
#print axioms not_forbidsEverySupportedPhysicalDeltaBOneOperator
#print axioms InvariantLineMass.radical_finrank_add_one
#print axioms ConcreteWeylNonzeroMass.fields_have_invariant_vector
#print axioms ConcreteWeylNonzeroMass.nonzeroMass_form_ne_zero
#print axioms ConcreteWeylNonzeroMass.not_all_symmetric_masses_zero
#print axioms ConcreteWeylNonzeroMass.nonzeroMass_radical_finrank
#print axioms ConcreteWeylNonzeroMass.exists_one_generation_nonzero_mass

end

end GUT.AuditWeylZeroModeSupport
