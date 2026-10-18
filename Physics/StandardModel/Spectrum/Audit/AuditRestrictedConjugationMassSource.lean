import Physics.StandardModel.Spectrum.ConjugationMassSource
import Physics.StandardModel.Spectrum.Audit.AuditIndependentProfileTotals
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Consumers require neither ambient unitarity nor common species totals.
The unequal-target consumer is conditional on actual matter and its target;
it is not an independent construction of an anomaly-consistent model. -/

set_option autoImplicit false

namespace GUT.StructuralConjugationMass.AuditRestricted

open SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors FiniteChargeProfiles
open StandardSMCharacterTarget InvariantWeylMass StandardModelLocalOperator

variable {G H E : Type*} [Group G] [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (restrict j rho))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
  (P : Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
  (c : ThreeConjugations j) (ht : HasTarget j rho B P s)

include hu ht in
theorem actual_zeroMode (i : Fin 15) (q : ChargeLabel H) (hq : 0 < smCharge P i q) :
    ∃ v : E, v ≠ 0 ∧ (∀ w, B.form v w = 0) ∧
      ∀ g, restrict j rho g v = keyCharacter (smReducedWeight i, q) g • v := by
  obtain ⟨v, hv, he⟩ := RestrictedUnitary.exists_zeroMode j rho B P s hu ht i q hq
  refine ⟨v, fun hz => hv (Subtype.ext hz), (B.mem_radical v).mp v.property, ?_⟩
  intro g
  exact congrArg Subtype.val (he g)

example (hQ : 0 < total P.quark) (hD : 0 < total P.down) :
    OrbitCompatible P ∧
      ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (RestrictedUnitary.spectrum j rho B hu) :=
  ⟨profiles_compatible j rho B P s c ht,
    RestrictedUnitary.selection_rule_obstruction j rho B P s hu hQ hD c ht⟩

example (hambient : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    spectrum j rho hambient B = RestrictedUnitary.spectrum j rho B hu := rfl

section FiniteResidual
open FiniteChargeProfiles.AuditIndependentTotals

include c in
theorem unequal_target_endpoint
    (rho' : Representation ℂ (G × Residual) E) (B' : SymmetricMass (restrict j rho'))
    (hu' : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho'))
    (s' : ChargeLabel Residual →₀ ℤ) (ht' : HasTarget j rho' B' unequal s') :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (RestrictedUnitary.spectrum j rho' B' hu') := by
  exact RestrictedUnitary.selection_rule_obstruction j rho' B' unequal s' hu'
    (by simp [unequal]) (by simp [unequal]) c ht'

end FiniteResidual
end GUT.StructuralConjugationMass.AuditRestricted

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Restricted mass imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.StructuralConjugationMass.RestrictedUnitary.spectrum,
    ``GUT.StructuralConjugationMass.RestrictedUnitary.spectrum_nonneg,
    ``GUT.StructuralConjugationMass.RestrictedUnitary.chiral_spectrum,
    ``GUT.StructuralConjugationMass.RestrictedUnitary.exists_zeroMode,
    ``GUT.StructuralConjugationMass.RestrictedUnitary.chargesSupported,
    ``GUT.StructuralConjugationMass.RestrictedUnitary.exists_actual_signature_pair,
    ``GUT.StructuralConjugationMass.RestrictedUnitary.selection_rule_obstruction,
    ``GUT.StructuralConjugationMass.spectrum_eq_restricted,
    ``GUT.StructuralConjugationMass.AuditRestricted.actual_zeroMode,
    ``GUT.StructuralConjugationMass.AuditRestricted.unequal_target_endpoint]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Restricted mass: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Restricted mass: import boundary and {declarations.length} strict transitive axiom checks passed"
