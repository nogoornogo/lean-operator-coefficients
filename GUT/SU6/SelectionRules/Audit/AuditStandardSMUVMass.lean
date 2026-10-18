import GUT.SU6.SelectionRules.Models.StandardSMUVMass

/-!
Persistent audit of exterior branching and the actual SU(6) mass example.
This constructs the mass and its spectrum; neither rank nor tensor
nonvanishing is an input. Lorentz/Grassmann quotients remain separate.
-/

set_option autoImplicit false

namespace GUT.AuditStandardSMUVMass

noncomputable section

open SMEpsilonTensor StandardSMExterior
open scoped TensorProduct

theorem color_orientation :
    (branch (wedge (colorBasis 0, (0, 0)) (colorBasis 1, (0, 0)))).1 (colorBasis 2) = 1 ∧
    (branch (wedge (colorBasis 1, (0, 0)) (colorBasis 0, (0, 0)))).1 (colorBasis 2) = -1 := by
  simp only [branch_wedge_split, pair_color_color]
  change eps3 (colorBasis 0) (colorBasis 1) (colorBasis 2) = 1 ∧
    eps3 (colorBasis 1) (colorBasis 0) (colorBasis 2) = -1
  simp [eps3, colorBasis]

theorem mixed_orientation :
    (branch (wedge (0, (weakBasis 0, 0)) (colorBasis 0, (0, 0)))).2.1 =
      -(colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) := by
  simp [pair]

theorem electron_orientation :
    (branch (wedge (0, (weakBasis 0, 0)) (0, (weakBasis 1, 0)))).2.2.1 1 = 1 := by
  simp

open StandardSMUVMass StandardSMUVFields

theorem actual_uv_benchmark (H : Type*) [CommGroup H] :
    Module.finrank ℂ UV = 27 ∧ (mass H).form ≠ 0 ∧
      Module.finrank ℂ (ZeroModes H) = 15 ∧ qque H ≠ 0 ∧ duql H ≠ 0 ∧
      (∀ g x, qque H (qqueRho H g x) = qque H x) ∧
      (∀ g x, duql H (duqlRho H g x) = duql H x) :=
  ⟨uv_finrank, mass_nonzero H, radical_finrank H, qque_nonzero H, duql_nonzero H,
    qque_invariant H, duql_invariant H⟩

example : Module.finrank ℂ (ZeroModes (Multiplicative (ZMod 2))) = 15 := radical_finrank _
example : (mass Unit).form ≠ 0 := mass_nonzero _

theorem zero_mass_not_fifteen :
    Module.finrank ℂ (InvariantWeylMass.SymmetricMass.zero (rho Unit)).radical.toSubmodule = 27 := by
  rw [InvariantWeylMass.SymmetricMass.radical_zero]
  simpa using uv_finrank

#print axioms StandardSMExterior.branch_bijective
#print axioms StandardSMExterior.branchIntertwiner
#print axioms StandardSMExterior.analyticEquiv
#print axioms StandardSMUVFields.uv_jointlyContinuous
#print axioms StandardSMUVFields.gaugeEquiv
#print axioms StandardSMUVFields.withResidualEquiv
#print axioms StandardSMUVFields.physicalRestriction_eq
#print axioms EquivariantWeylMassTransport.pullback
#print axioms EquivariantWeylMassTransport.radicalEquiv
#print axioms StandardSMUVMass.lightEquiv
#print axioms StandardSMUVMass.radical_character
#print axioms StandardSMUVMass.mass_nonzero
#print axioms StandardSMUVMass.radical_finrank
#print axioms StandardSMUVMass.qque_witness
#print axioms StandardSMUVMass.duql_witness
#print axioms StandardSMUVMass.qque_invariant
#print axioms StandardSMUVMass.duql_invariant
#print axioms actual_uv_benchmark
#print axioms color_orientation
#print axioms mixed_orientation
#print axioms electron_orientation
#print axioms zero_mass_not_fifteen

end

end GUT.AuditStandardSMUVMass
