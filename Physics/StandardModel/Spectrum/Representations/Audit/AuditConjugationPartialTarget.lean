import Physics.StandardModel.Spectrum.Representations.ConjugationPartialTarget
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Consumers of the local index condition, with actual zero-mass vectors
and recovery of the previous full-target interface on the same spectrum. -/

set_option autoImplicit false
namespace Physics.ConjugationPartialTarget.Audit
open SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors FiniteChargeProfiles
open StandardSMCharacterTarget InvariantWeylMass StandardModelLocalOperator
open StructuralConjugationMass

variable {G H E : Type*} [Group G] [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (B : SymmetricMass (restrict j rho))
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
  (P : Profiles (ChargeLabel H)) (c : ThreeConjugations j)

theorem actual_zeroMode (ht : HasPartialTarget j rho B hu P)
    (i : Fin 15) (q : ChargeLabel H) (hq : 0 < smCharge P i q) :
    ∃ v : E, v ≠ 0 ∧ (∀ w, B.form v w = 0) ∧
      ∀ g, restrict j rho g v = keyCharacter (smReducedWeight i, q) g • v := by
  obtain ⟨v, hv, he⟩ := exists_zeroMode j rho B hu P ht i q hq
  refine ⟨v, fun hz => hv (Subtype.ext hz), (B.mem_radical v).mp v.property, ?_⟩
  intro g
  exact congrArg Subtype.val (he g)

example (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (ht : HasPartialTarget j rho B hu P) :
    OrbitCompatible P ∧
      ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (RestrictedUnitary.spectrum j rho B hu) :=
  ⟨ConjugationPartialTarget.profiles_compatible j rho B hu P c ht,
    selection_rule_obstruction j rho B hu P hQ hD c ht⟩

include c in
theorem recover_full_target (hQ : 0 < total P.quark) (hD : 0 < total P.down)
    (s : ChargeLabel H →₀ ℤ) (ht : HasTarget j rho B P s) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (RestrictedUnitary.spectrum j rho B hu) :=
  selection_rule_obstruction j rho B hu P hQ hD c (of_full_target j rho B hu P s ht)

end Physics.ConjugationPartialTarget.Audit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Partial target imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.SMPartialTarget.MatchesSM,
    ``Physics.SMPartialTarget.of_full_target,
    ``Physics.SMPartialTarget.profile_eq,
    ``Physics.SMPartialTarget.coefficient_lower_bound,
    ``Physics.SMPartialTarget.chargesSupported_of_occupied,
    ``Physics.SMPartialTarget.add_of_dual_vanishes,
    ``Physics.ConjugationPartialTarget.HasPartialTarget,
    ``Physics.ConjugationPartialTarget.of_full_target,
    ``Physics.ConjugationPartialTarget.profiles_compatible,
    ``Physics.ConjugationPartialTarget.exists_zeroMode,
    ``Physics.ConjugationPartialTarget.chargesSupported,
    ``Physics.ConjugationPartialTarget.exists_actual_signature_pair,
    ``Physics.ConjugationPartialTarget.selection_rule_obstruction,
    ``Physics.ConjugationPartialTarget.Audit.actual_zeroMode,
    ``Physics.ConjugationPartialTarget.Audit.recover_full_target]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Partial target: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Partial target: import boundary and {declarations.length} strict transitive axiom checks passed"
