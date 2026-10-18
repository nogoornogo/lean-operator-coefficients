import Physics.StandardModel.Spectrum.ConjugationMassSource
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Audit the actual mass endpoint with only restricted mass invariance.
No action of a conjugating element on the radical is assumed. -/

set_option autoImplicit false

namespace GUT.StructuralConjugationMass.Audit

open SU5.MaximalTorus SU5.TorusCharacter StructuralConjugation
open StandardAbelianCharge FiniteAbelianChargeSectors FiniteChargeProfiles
open StandardSMCharacterTarget
open InvariantWeylMass StandardModelLocalOperator

variable {G H E : Type*} [Group G] [CommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (j : Torus →* G) (rho : Representation ℂ (G × H) E)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
  (B : SymmetricMass (restrict j rho)) (c : ThreeConjugations j)
  (s : ChargeLabel H →₀ ℤ) (F : Family (ChargeLabel H))
  (ht : HasTarget j rho B F.profiles s)

example : OrbitCompatible F.profiles ∧
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (spectrum j rho hu B) :=
  ⟨profiles_compatible j rho B F.profiles s c ht,
    selection_rule_obstruction j rho hu B s F c ht⟩

-- Check actual ambient fields, including the zero-mass equation, rather than
-- only a positive coefficient in a supplied formal polynomial.
example (i : Fin 15) (q : ChargeLabel H) (hq : 0 < smCharge F.profiles i q) :
    ∃ v : E, v ≠ 0 ∧ (∀ w, B.form v w = 0) ∧
      ∀ g, restrict j rho g v = keyCharacter (StandardSMCharacterTarget.smReducedWeight i, q) g • v := by
  obtain ⟨v, hv, he⟩ := exists_zeroMode j rho hu B F.profiles s ht i q hq
  refine ⟨v, fun hz => hv (Subtype.ext hz), (B.mem_radical v).mp v.property, ?_⟩
  intro g
  exact congrArg Subtype.val (he g)

example : 0 < F.generations := F.positive

end GUT.StructuralConjugationMass.Audit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Conjugation mass imports UV application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.StructuralConjugationMass.restricted_unitary,
    ``GUT.StructuralConjugationMass.HasTarget,
    ``GUT.StructuralConjugationMass.source_target,
    ``GUT.StructuralConjugationMass.profiles_compatible,
    ``GUT.StructuralConjugationMass.spectrum,
    ``GUT.StructuralConjugationMass.spectrum_nonneg,
    ``GUT.StructuralConjugationMass.chiral_spectrum,
    ``GUT.StructuralConjugationMass.exists_zeroMode,
    ``GUT.StructuralConjugationMass.chargesSupported,
    ``GUT.StructuralConjugationMass.exists_actual_signature_pair,
    ``GUT.StructuralConjugationMass.selection_rule_obstruction]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conjugation mass: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conjugation mass: import boundary and {declarations.length} strict transitive axiom checks passed"
