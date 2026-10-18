import Physics.StandardModel.Spectrum.ConjugationDualIndex
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! No global light target is an input to actual dual-index invariance. -/
set_option autoImplicit false

namespace GUT.ConjugationDualIndex.Audit
open SU5.MaximalTorus StructuralConjugation StandardAbelianCharge
open InvariantWeylMass FiniteAbelianChargeSectors

example {G H E : Type*} [Group G] [CommGroup H] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (j : Torus →* G) (rho : Representation ℂ (G × H) E)
    (B : SymmetricMass (restrict j rho))
    (hu : UnitaryMultiplicity.IsUnitaryRepresentation (restrict j rho))
    (p : Equiv.Perm (Fin 5)) (c : Realizes j p) (key : ResolvedKey (ChargeLabel H)) :
    dualIndex j rho B hu (permuteKey p key) = dualIndex j rho B hu key :=
  coeff_permute j rho B hu p c key

end GUT.ConjugationDualIndex.Audit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Dual index imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.AbelianActualSpectrum.coeff_comp_eq_of_eval_invariant,
    ``GUT.ConjugationDualIndex.coordinateEquiv,
    ``GUT.ConjugationDualIndex.keyCharacter_permute,
    ``GUT.ConjugationDualIndex.dualIndex,
    ``GUT.ConjugationDualIndex.dualIndex_apply,
    ``GUT.ConjugationDualIndex.fullDual_eval,
    ``GUT.ConjugationDualIndex.coeff_permute]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Dual index: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Dual index: import boundary and {declarations.length} strict transitive axiom checks passed"
