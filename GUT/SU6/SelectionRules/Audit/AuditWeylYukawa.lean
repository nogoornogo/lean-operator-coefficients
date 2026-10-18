import GUT.SU6.SelectionRules.Benchmarks.WeylYukawaBenchmark
import Physics.FieldTheory.Mass.WeylMassTwoTorsion

/-!
# Audit: scalar-linear symmetric Yukawa source bridge

Checks a nonzero full-SU(6) invariant tensor, a nontrivial order-two Majorana
sector, and a continuous-geometry example with nonzero Yukawa and exact
15-mode radical. This is not an amplitude or full proton-tensor assertion.
-/

set_option autoImplicit false

namespace GUT.AuditWeylYukawa

noncomputable section

open WeylYukawaMass ContinuousWeylYukawaModel StandardSMCharacterTarget ConcreteSU6PhysicalTarget

example : ∃ M : Model (Multiplicative (ZMod 2)),
    M.generations = 1 ∧ M.sector.bareMass.form = 0 ∧ M.sector.yukawa.toLinearMap ≠ 0 ∧
      Module.finrank ℂ M.sector.mass.radical.toSubmodule = 15 ∧
      PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical =
        exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  WeylYukawaBenchmark.FullMass.exists_yukawa_sm_radical _

example : Nonempty (StandardModelLocalOperator.SupportedInvariantOperator
    (PhysicalWeylZeroModeSupport.lightSpectrum
      (WeylYukawaBenchmark.FullMass.model (Multiplicative (ZMod 2))).toMassModel.toPhysical)) :=
  ⟨(WeylYukawaBenchmark.FullMass.model _).supportedInvariantOperator
    (by change (0 : ℤ) < 1; norm_num)⟩

example : (Sector.ofMassAsYukawa WeylMassTwoTorsion.majoranaMass).mass =
    WeylMassTwoTorsion.majoranaMass := Sector.ofMassAsYukawa_mass _

/-- A nonzero coupling alone does not force a nonzero induced mass. -/
def zeroVEVSector : Sector (Representation.trivial ℂ ℤˣ ℂ) WeylMassTwoTorsion.signRepresentation where
  bareMass := InvariantWeylMass.SymmetricMass.zero _
  yukawa := EquivariantYukawa.ofMass WeylMassTwoTorsion.majoranaMass
  vacuum := DiracYukawaMass.InvariantVacuum.zero

example : zeroVEVSector.mass.form = 0 := by simp [zeroVEVSector, Sector.mass,
  DiracYukawaMass.InvariantVacuum.zero, InvariantWeylMass.SymmetricMass.zero]

example : zeroVEVSector.yukawa.toLinearMap ≠ 0 := by
  apply EquivariantYukawa.ofMass_nonzero
  intro h
  have he := LinearMap.congr_fun (LinearMap.congr_fun h 1) 1
  norm_num [WeylMassTwoTorsion.majoranaMass] at he

#print axioms EquivariantYukawa.tensorIntertwiner
#print axioms Sector.mass
#print axioms Sector.ofBareMass_mass
#print axioms Sector.ofMassAsYukawa_mass
#print axioms atVacuumOn
#print axioms vacuumStabilizer
#print axioms atVacuumStabilizer
#print axioms Model.hyperchargePair_eq_standard
#print axioms Model.supportedInvariantOperator
#print axioms Model.not_forbidsEverySupportedPhysicalDeltaBOneOperator
#print axioms Model.not_forbidsBothOrientations
#print axioms Model.ofMassAsYukawa_toMassModel
#print axioms WeylYukawaBenchmark.AmbientPair.tensor_nonzero
#print axioms WeylYukawaBenchmark.AmbientPair.invariant
#print axioms WeylYukawaBenchmark.FullMass.yukawa_nonzero
#print axioms WeylYukawaBenchmark.FullMass.radical_finrank
#print axioms WeylYukawaBenchmark.FullMass.lightSpectrum
#print axioms WeylYukawaBenchmark.FullMass.exists_yukawa_sm_radical

end

end GUT.AuditWeylYukawa
