import GUT.SU6.SelectionRules.Benchmarks.WeylMassFamilyBenchmark
import GUT.SU6.SelectionRules.Benchmarks.WeylYukawaBenchmark

open Physics

/-! MASS-3 checks the actual endpoint, legacy compatibility, and nonlinear
non-vacuity. The benchmark is on the existing unbroken group, not a new
full-SU(6) scalar geometry. -/

set_option autoImplicit false

namespace GUT.AuditWeylMassFamilyModel

noncomputable section

open ContinuousWeylFamilyModel StandardModelLocalOperator

variable {H : Type*} [CommGroup H]

example (M : ContinuousWeylYukawaModel.Model H) :
    (Model.ofLinearModel M).toMassModel = M.toMassModel := Model.ofLinearModel_toMassModel M

example : (Model.ofLinearModel (WeylYukawaBenchmark.FullMass.model H)).toMassModel =
    (WeylMassFamilyBenchmark.model H).toMassModel := by
  rw [Model.ofLinearModel_toMassModel, WeylYukawaBenchmark.FullMass.toMassModel,
    WeylMassFamilyBenchmark.toMassModel]

example : Nonempty (SupportedInvariantOperator (PhysicalWeylZeroModeSupport.lightSpectrum
    (WeylMassFamilyBenchmark.model (Multiplicative (ZMod 2))).toMassModel.toPhysical)) :=
  ⟨WeylMassFamilyBenchmark.supportedInvariantOperator⟩

example : ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
    (PhysicalWeylZeroModeSupport.lightSpectrum
      (WeylMassFamilyBenchmark.model (Multiplicative (ZMod 2))).toMassModel.toPhysical) :=
  (WeylMassFamilyBenchmark.model _).not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (by change (0 : ℤ) < 1; norm_num)

example : ¬ WeylConjugateOperator.ForbidsBothOrientations
    (PhysicalWeylZeroModeSupport.lightSpectrum
      (WeylMassFamilyBenchmark.model (Multiplicative (ZMod 2))).toMassModel.toPhysical) :=
  (WeylMassFamilyBenchmark.model _).finiteAbelian_not_forbidsBothOrientations

/-- The zero VEV does not remove the nonzero coupling. -/
example : (WeylMassFamilyBenchmark.zeroVacuumSector (H := H)).family.toFun (1 : ℂ) ≠ 0 := by
  rw [WeylMassFamilyBenchmark.zeroVacuum_family]
  exact WeylMassFamilyBenchmark.family_at_one_nonzero

example : (WeylMassFamilyBenchmark.zeroVacuumSector (H := H)).mass.form = 0 := by
  rw [WeylMassFamilyBenchmark.zeroVacuum_mass]
  rfl

example : Continuous (fun p : (WeylMassFamilyBenchmark.model H).scalar.V × _ × _ =>
    (WeylMassFamilyBenchmark.model H).sector.family.toFun p.1 p.2.1 p.2.2) :=
  (WeylMassFamilyBenchmark.model H).continuous_family

#print axioms Model.toMassModel
#print axioms Model.hyperchargePair_eq_standard
#print axioms Model.proton_functionals_eq_zero
#print axioms Model.supportedInvariantOperator
#print axioms Model.not_forbidsEverySupportedPhysicalDeltaBOneOperator
#print axioms Model.not_forbidsBothOrientations
#print axioms Model.finiteAbelian_not_forbidsBothOrientations
#print axioms Model.ofLinearModel
#print axioms Model.ofLinearModel_toMassModel
#print axioms Model.ofLinearModel_mass
#print axioms Model.ofLinearModel_lightSpectrum
#print axioms Model.ofMassAsPower_toMassModel
#print axioms WeylMassFamilyBenchmark.toMassModel
#print axioms WeylMassFamilyBenchmark.family_at_one_nonzero
#print axioms WeylMassFamilyBenchmark.family_not_additive
#print axioms WeylMassFamilyBenchmark.mass_nonzero
#print axioms WeylMassFamilyBenchmark.radical_finrank
#print axioms WeylMassFamilyBenchmark.lightSpectrum
#print axioms WeylMassFamilyBenchmark.supportedInvariantOperator
#print axioms WeylMassFamilyBenchmark.zeroVacuum_family
#print axioms WeylMassFamilyBenchmark.zeroVacuum_mass
#print axioms WeylMassFamilyBenchmark.zeroVacuum_radical
#print axioms WeylMassFamilyBenchmark.exists_nonlinear_sm_radical

end
end GUT.AuditWeylMassFamilyModel
