import GUT.SU6.SelectionRules.Models.PhysicalProfileSource
import GUT.SU6.SelectionRules.Models.ContinuousWeylFamilyModel

open Physics

/-!
# Continuous SU(6) models with family-dependent charge profiles

One exact dual light target supplies hypercharge rigidity, orbit-profile
equalities, and actual supported neutral signatures. No charge equality or
support is a model field. The result remains a scoped selection rule.
-/

set_option autoImplicit false

namespace GUT.ContinuousProfileModel

noncomputable section

open FinalNoGoAssembly PhysicalMassSpectrumBridge StandardSMCharacterTarget
open InvariantWeylMass StandardModelLocalOperator UnitaryVirtualRealization
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)

structure Model (H : Type*) [CommGroup H] where
  geometry : ContinuousHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  nonnegative : ∀ s ∈ matter, 0 ≤ s.coeff
  mass : SymmetricMass
    (ordinaryPositiveRepresentation geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  profile : FiniteChargeProfiles.Family (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : ProfileZeroModeSupport.HasTarget
    (ordinaryPositiveRepresentation geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter)
    mass profile.profiles singlets

variable {H : Type*} [CommGroup H]

namespace Model

def fields (M : Model H) : ActualUnitaryGroupRepresentation (CombinedGroup H) :=
  ordinaryPositiveRepresentation M.geometry.hyperchargePair.1 M.geometry.hyperchargePair.2 M.matter

def lightSpectrum (M : Model H) := ProfileZeroModeSupport.spectrum M.fields M.mass

theorem source_conclusions (M : Model H) :
    (M.geometry.hyperchargePair.1 = -2 ∧ M.geometry.hyperchargePair.2 = 3) ∧
      FiniteChargeProfiles.OrbitCompatible M.profile.profiles :=
  PhysicalProfileSource.source_conclusions _ _ M.matter M.nonnegative M.mass
    M.profile M.singlets M.lightTarget

theorem hyperchargePair_eq_standard (M : Model H) : M.geometry.hyperchargePair = (-2, 3) :=
  Prod.ext M.source_conclusions.1.1 M.source_conclusions.1.2

theorem profiles_compatible (M : Model H) : FiniteChargeProfiles.OrbitCompatible M.profile.profiles :=
  M.source_conclusions.2

theorem actual_signature_pair (M : Model H) :
    ∃ Q D : SupportedInvariantOperator M.lightSpectrum,
      Q.operator = .qque ∧ D.operator = .duql ∧ Q.charges = D.charges ∧
      ∀ i : Fin 15, ∃ v : M.mass.radical.toSubmodule, v ≠ 0 ∧
        ∀ g, M.mass.radical.toRepresentation g v = keyMonoidHom (smResolvedKey Q.charges i) g • v :=
  ProfileZeroModeSupport.exists_actual_signature_pair M.fields M.mass M.singlets M.profile
    M.lightTarget M.profiles_compatible

theorem selection_rule_obstruction (M : Model H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator M.lightSpectrum :=
  ProfileZeroModeSupport.not_forbidsEverySupportedPhysicalDeltaBOneOperator
    M.fields M.mass M.singlets M.profile M.lightTarget M.profiles_compatible

def ofLegacy (M : ContinuousWeylModel.ContinuousWeylMassModel H) (hn : 0 < M.generations) :
    Model H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  mass := M.mass
  profile :=
    { profiles := FiniteChargeProfiles.pure M.generations.toNat M.charges
      generations := M.generations.toNat
      positive := by omega
      totals := FiniteChargeProfiles.pure_totals _ _ }
  singlets := M.singlets
  lightTarget := by
    unfold ProfileZeroModeSupport.HasTarget
    rw [FiniteChargeProfiles.targetWithSinglets_pure,
      show (M.generations.toNat : ℤ) = M.generations by omega]
    exact M.lightTarget.standard

@[simp] theorem ofLegacy_mass (M : ContinuousWeylModel.ContinuousWeylMassModel H)
    (hn : 0 < M.generations) : (ofLegacy M hn).mass = M.mass := rfl

@[simp] theorem ofLegacy_lightSpectrum (M : ContinuousWeylModel.ContinuousWeylMassModel H)
    (hn : 0 < M.generations) :
    (ofLegacy M hn).lightSpectrum = PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical := rfl

end Model

/-- MASS-3's scalar-family interface, with the positive profile target in
place of a single charge per species. The unbroken-group scope is unchanged. -/
structure ScalarModel (H : Type*) [CommGroup H] where
  geometry : ContinuousHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  nonnegative : ∀ s ∈ matter, 0 ≤ s.coeff
  scalar : ActualUnitaryGroupRepresentation (CombinedGroup H)
  sector : WeylMassFamily.Sector scalar.rho
    (ordinaryPositiveRepresentation geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  continuous_family : Continuous (fun p : scalar.V × _ × _ =>
    sector.family.toFun p.1 p.2.1 p.2.2)
  profile : FiniteChargeProfiles.Family (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : ProfileZeroModeSupport.HasTarget
    (ordinaryPositiveRepresentation geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter)
    sector.mass profile.profiles singlets

namespace ScalarModel

def toMassModel (M : ScalarModel H) : Model H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  mass := M.sector.mass
  profile := M.profile
  singlets := M.singlets
  lightTarget := M.lightTarget

theorem selection_rule_obstruction (M : ScalarModel H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator M.toMassModel.lightSpectrum :=
  M.toMassModel.selection_rule_obstruction

def ofLegacy (M : ContinuousWeylFamilyModel.Model H) (hn : 0 < M.generations) : ScalarModel H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  scalar := M.scalar
  sector := M.sector
  continuous_family := M.continuous_family
  profile := (Model.ofLegacy M.toMassModel hn).profile
  singlets := M.singlets
  lightTarget := (Model.ofLegacy M.toMassModel hn).lightTarget

@[simp] theorem ofLegacy_toMassModel (M : ContinuousWeylFamilyModel.Model H)
    (hn : 0 < M.generations) :
    (ofLegacy M hn).toMassModel = Model.ofLegacy M.toMassModel hn := rfl

end ScalarModel

end

end GUT.ContinuousProfileModel
