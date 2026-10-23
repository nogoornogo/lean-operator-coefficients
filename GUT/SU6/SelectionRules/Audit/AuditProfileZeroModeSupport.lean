import GUT.SU6.SelectionRules.Models.ProfileZeroModeSupport
import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylFullMass
import Physics.StandardModel.Spectrum.Charges.Audit.AuditProfileChiralIndex

open Physics

/-! Actual-radical regression of the profile interface, with nonzero mass
and with extra zero modes. No supplied eigenvectors or UV support premise. -/

set_option autoImplicit false

namespace GUT.AuditProfileZeroModeSupport

noncomputable section

open ProfileZeroModeSupport StandardSMCharacterTarget StandardWeylMassSource
open FiniteChargeProfiles StandardModelLocalOperator StandardBranchProtonObstruction

abbrev Residual := Multiplicative (ZMod 2)

def fullFamily : Family (ChargeLabel Residual) where
  profiles := FiniteChargeProfiles.pure 1 (ConcreteWeylFullMass.model Residual).charges
  generations := 1
  positive := by decide
  totals := pure_totals _ _

theorem fullFamily_compatible : OrbitCompatible fullFamily.profiles := ⟨rfl, rfl, rfl⟩

theorem full_target :
    HasTarget (ordinaryFields (ConcreteWeylFullMass.model Residual).matter)
      (ConcreteWeylFullMass.model Residual).mass fullFamily.profiles
      (ConcreteWeylFullMass.model Residual).singlets := legacy_target _ 1 rfl

theorem full_mass_actual_pair :
    let M := ConcreteWeylFullMass.model Residual
    ∃ Q D : SupportedInvariantOperator (spectrum (ordinaryFields M.matter) M.mass),
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom (smResolvedKey Q.charges i) g • v :=
  exists_actual_signature_pair _ _ _ fullFamily full_target fullFamily_compatible

/-- The old nonzero mass with 26 light modes is also accepted; exact
fifteen-dimensional radical spectrum is not required. -/
theorem extra_modes_supported (i : Fin 15) :
    let M := ConcreteWeylNonzeroMass.model Residual
    ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom (smResolvedKey M.charges i) g • v := by
  let M := ConcreteWeylNonzeroMass.model Residual
  apply all_occupied_zeroModes (ordinaryFields M.matter) M.mass
    (FiniteChargeProfiles.pure 1 M.charges) M.singlets (legacy_target M 1 rfl) M.charges
  exact (occupied_pure_iff 1 (by decide) _ _).mpr rfl

#print axioms chiral_spectrum
#print axioms profile_le_spectrum
#print axioms ProfileZeroModeSupport.exists_zeroMode
#print axioms all_occupied_zeroModes
#print axioms ProfileZeroModeSupport.chargesSupported
#print axioms exists_actual_signature_pair
#print axioms ProfileZeroModeSupport.not_forbidsEverySupportedPhysicalDeltaBOneOperator
#print axioms legacy_spectrum
#print axioms legacy_target
#print axioms full_target
#print axioms full_mass_actual_pair
#print axioms extra_modes_supported

end

end GUT.AuditProfileZeroModeSupport
