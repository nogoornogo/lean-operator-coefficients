import GUT.SU6.SelectionRules.Benchmarks.ContinuousWeylBenchmark

open Physics

/-!
# Audit of semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality for symmetric linearized mass sectors

The endpoint uses actual radical support and the declared operator-signature
API. Matter actions commute strictly with SU(6); mass invariance is under
the physical torus times the residual group. The dual light target remains
an infrared applicability field. No amplitude or general Yukawa semantics
is asserted. Actual constructors below check non-vacuity independently of
the conditional theorems.
-/

set_option autoImplicit false

namespace GUT.AuditContinuousWeylModel

noncomputable section

open ContinuousWeylModel PhysicalWeylMassSource StandardModelLocalOperator

example : ∃ M : ContinuousWeylMassModel PUnit.{1}, M.generations = 1 :=
  ContinuousWeylBenchmark.exists_one_generation_model _

example : ∃ M : ContinuousWeylMassModel (Multiplicative (ZMod 2)), M.generations = 1 :=
  ContinuousWeylBenchmark.exists_one_generation_model _

example : Nonempty (SupportedInvariantOperator (PhysicalWeylZeroModeSupport.lightSpectrum
    (ContinuousWeylBenchmark.model (Multiplicative (ZMod 2))).toPhysical)) :=
  ⟨(ContinuousWeylBenchmark.model _).supportedInvariantOperator (by change (0 : ℤ) < 1; norm_num)⟩

example : ¬ WeylConjugateOperator.ForbidsBothOrientations
    (PhysicalWeylZeroModeSupport.lightSpectrum
      (ContinuousWeylBenchmark.model (Multiplicative (ZMod 2))).toPhysical) :=
  (ContinuousWeylBenchmark.model _).finiteAbelian_not_forbidsBothOrientations

example (M : ContinuousWeylMassModel (Multiplicative (ZMod 2))) (hn : 0 < M.generations)
    (i : Fin 15) : ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v =
        StandardSMCharacterTarget.keyMonoidHom (StandardSMCharacterTarget.smResolvedKey M.charges i) g • v :=
  PhysicalWeylZeroModeSupport.all_sm_zeroModes M.toPhysical hn i

#print axioms fields_character
#print axioms dualResolved_of_lightTarget
#print axioms lightTarget_of_dualResolved
#print axioms PhysicalWeylModel.hypercharge_eq_standard
#print axioms PhysicalWeylModel.su5OrbitCompatible
#print axioms PhysicalWeylModel.proton_functionals_eq_zero
#print axioms PhysicalWeylZeroModeSupport.lightSpectrum_chiralDifference
#print axioms PhysicalWeylZeroModeSupport.all_sm_zeroModes
#print axioms PhysicalWeylZeroModeSupport.all_conjugate_sm_zeroModes
#print axioms ContinuousWeylMassModel.hyperchargePair_eq_standard
#print axioms ContinuousWeylMassModel.proton_functionals_eq_zero
#print axioms ContinuousWeylMassModel.supportedInvariantOperator
#print axioms ContinuousWeylMassModel.not_forbidsEverySupportedPhysicalDeltaBOneOperator
#print axioms ContinuousWeylMassModel.exists_invariant_operator_or_conjugate
#print axioms ContinuousWeylMassModel.not_forbidsBothOrientations
#print axioms ContinuousWeylMassModel.finiteAbelian_not_forbidsBothOrientations
#print axioms ContinuousWeylBenchmark.standardSource_dualTarget
#print axioms ContinuousWeylBenchmark.ofStandardWithZeroMass
#print axioms ContinuousWeylBenchmark.model_mass_zero
#print axioms ContinuousWeylBenchmark.exists_one_generation_model

end

end GUT.AuditContinuousWeylModel
