import GUT.SU6.SelectionRules.Models.StandardSMUVYukawa
import GUT.SU6.SelectionRules.Models.StandardSMContinuousTensor

open Physics

open Math

/-! Persistent audit of the universal scalar/VEV completion. The scalar
representation and Yukawa family are fixed before the mass/VEV is chosen.
No scalar potential, exact SM stabilizer, or amplitude is assumed. -/

set_option autoImplicit false

namespace GUT.AuditStandardSMUVYukawa

noncomputable section

open StandardSMUVYukawa StandardSMUVFields

example : FiniteDimensional ℂ scalar.V := inferInstance

theorem scalar_continuous : ContinuousRepresentationScope.IsJointlyContinuous scalar.rho :=
  scalar.continuous_action

theorem scalar_unitary : CompactEmbeddingClassification.IsUnitaryRepresentation scalar.rho :=
  scalar.unitary

theorem full_su6_invariance (g : ActualRestriction.SU6) (s : scalar.V) (x y : UV) :
    yukawa.toLinearMap (scalar.rho g s) (uvRho g x) (uvRho g y) =
      yukawa.toLinearMap s x y := yukawa.invariant g s x y

theorem vacuum_benchmark (H : Type*) [CommGroup H] :
    bareMass.form = 0 ∧ yukawa.toLinearMap ≠ 0 ∧ tensor.toLinearMap ≠ 0 ∧
      vacuum H ≠ 0 ∧
      (∀ g, scalar.rho (StandardSMGroup.withResidual H g) (vacuum H) = vacuum H) ∧
      mass H = StandardSMUVMass.mass H ∧ (mass H).form ≠ 0 ∧
      Module.finrank ℂ (mass H).radical.toSubmodule = 15 :=
  ⟨bare_mass_zero, yukawa_nonzero, tensor_nonzero, vacuum_nonzero H,
    vacuum_fixed H, mass_eq H, mass_nonzero H, radical_finrank H⟩

example : vacuum (Multiplicative (ZMod 2)) ≠ 0 := vacuum_nonzero _

example : Module.finrank ℂ (mass Unit).radical.toSubmodule = 15 := radical_finrank _

theorem continuous_endpoint (H : Type*) [CommGroup H] :
    HEq (StandardSMOrdinaryMass.continuousModel H).mass (StandardSMOrdinaryMass.mass H) ∧
      (StandardSMOrdinaryMass.continuousModel H).mass.form ≠ 0 ∧
      Module.finrank ℂ (StandardSMOrdinaryMass.continuousModel H).mass.radical.toSubmodule = 15 ∧
      StandardSMContinuousTensor.qque H ≠ 0 ∧ StandardSMContinuousTensor.duql H ≠ 0 :=
  ⟨StandardSMOrdinaryMass.continuous_mass_heq H,
    StandardSMOrdinaryMass.continuous_mass_nonzero H,
    StandardSMOrdinaryMass.continuous_radical_finrank H,
    StandardSMContinuousTensor.qque_nonzero H, StandardSMContinuousTensor.duql_nonzero H⟩

/-- A nonzero coupling does not force a nonzero mass at every VEV. -/
theorem zero_vev_control (H : Type*) [CommGroup H] :
    yukawa.toLinearMap ≠ 0 ∧ (zeroVacuumMass H).form = 0 ∧
      Module.finrank ℂ (zeroVacuumMass H).radical.toSubmodule = 27 := by
  refine ⟨yukawa_nonzero, ?_, zeroVacuum_radical_finrank H⟩
  rw [zeroVacuumMass_eq]
  rfl

#print axioms SymmetricScalarYukawa.symmetricForms
#print axioms SymmetricScalarYukawa.yukawa
#print axioms SymmetricScalarYukawa.fixed_iff
#print axioms SymmetricScalarYukawa.inducedMass_eq
#print axioms ContinuousSymmetricScalar.matrixCoordinates_injective
#print axioms ContinuousSymmetricScalar.seed_jointlyContinuous
#print axioms UnitarySymmetricScalar.model
#print axioms UnitarySymmetricScalar.algebraEquiv
#print axioms UnitarySymmetricScalar.vacuum_fixed_iff
#print axioms UnitarySymmetricScalar.inducedMass_eq
#print axioms scalar_continuous
#print axioms scalar_unitary
#print axioms full_su6_invariance
#print axioms unbroken_le_stabilizer
#print axioms vacuum_mass_form
#print axioms ordinary_form
#print axioms vacuum_benchmark
#print axioms continuous_endpoint
#print axioms zero_vev_control

end

end GUT.AuditStandardSMUVYukawa
