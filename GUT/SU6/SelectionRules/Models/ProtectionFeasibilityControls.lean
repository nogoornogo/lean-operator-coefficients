import GUT.SU6.SelectionRules.Models.CyclicProtectionFeasibility
import Physics.StandardModel.Operators.Selection.InverseCyclicSMYukawa
import Physics.StandardModel.Operators.BaryonOne.Qque.S3QqueTensorSamples

/-! Existing concrete models test the new admission boundary. -/
namespace GUT.SU6ProtectionFeasibility.Controls
set_option autoImplicit false
noncomputable section
open Math Physics Representation
open FiniteChargeProfiles FiniteAbelianChargeSectors InvariantWeylMass UnitaryVirtualRealization

/-- The named protecting infrared input has an actual radical and allowed Yukawas. -/
theorem lepton_parity_mass_and_yukawa :
    Nonempty (Equiv InverseCyclicSMRealization.mass.radical.toRepresentation
      InverseCyclicSMRealization.light) ∧
    InverseCyclicSMRealization.mass.form ≠ 0 ∧
    InverseCyclicSMYukawa.up ≠ 0 ∧ InverseCyclicSMYukawa.down ≠ 0 ∧
    InverseCyclicSMYukawa.electron ≠ 0 :=
  ⟨⟨InverseCyclicSMRealization.radicalEquiv⟩,
    InverseCyclicSMRealization.spectator_mass_nonzero,
    InverseCyclicSMYukawa.up_nonzero, InverseCyclicSMYukawa.down_nonzero,
    InverseCyclicSMYukawa.electron_nonzero⟩

/-- Actual all-degree derivative-free IR prohibition does not imply a UV lift. -/
theorem lepton_parity_ir_success_uv_failure
    (R : ActualUnitaryGroupRepresentation
      (ChargedAmbientRealization.AmbientGroup (CyclicCharge.Group 2)))
    (B : SymmetricMass (SU6.PhysicalChainSource.physicalFields R).rho)
    (s : ChargeLabel (CyclicCharge.Group 2) →₀ ℤ) :
    (∀ n m, ∀ f : ComposableBLSupport.Input
      InverseCyclicSMRealization.fermionFlavor InverseCyclicSMRealization.higgsFlavor
      InverseLeptonParitySelection.target n m, f = 0) ∧
    ¬ ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure 3 (charges (0 : ZMod 2) 1)) s :=
  ⟨InverseCyclicSMRealization.all_B1_forbidden,
    lepton_parity_no_target R B 3 (by norm_num) s⟩

/-- Changing the residual group can remove qque without supplying a usable
uniform SU(6) flavor dictionary or full-rank neutral-Higgs maps. -/
theorem unequal_s3_screen :
    SelectionCriteria.Forbidden (QquePhysicalExteriorCompleteness.Sector
      S3QqueTensorSamples.q S3QqueTensorSamples.trivial S3QqueTensorSamples.sign) ∧
    SelectionCriteria.Allowed (QquePhysicalExteriorCompleteness.Sector
      S3QqueTensorSamples.q S3QqueTensorSamples.sign S3QqueTensorSamples.sign) ∧
    (∀ f : IntertwiningMap S3QqueTensorSamples.q S3QqueTensorSamples.trivial,
      ¬ Function.Injective f) ∧
    (∀ f : IntertwiningMap S3QqueTensorSamples.q S3QqueTensorSamples.sign, f = 0) :=
  ⟨S3QqueTensorSamples.forbidden_permutation_trivial_sign,
    S3QqueTensorSamples.allowed_permutation_sign_sign,
    S3QqueTensorSamples.q_to_trivial_not_injective,
    S3QqueTensorSamples.no_q_to_sign⟩

end
end GUT.SU6ProtectionFeasibility.Controls
