import Physics.StandardModel.Spectrum.ConjugationSource
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! SC-1 boundary audit. The source is arbitrary ambient matter; only three
actual conjugation identities enter the charge-profile conclusion. -/

set_option autoImplicit false

namespace GUT.StructuralConjugation.Audit

open SU5 SU5.MaximalTorus StandardAbelianCharge FiniteAbelianChargeSectors
open FiniteChargeProfiles StandardWeylDualTarget

section
variable {G H E : Type*} [Group G] [CommGroup H]
  [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

example (j : Torus →* G) (c : ThreeConjugations j)
    (rho : Representation ℂ (G × H) E) (P : Profiles (ChargeLabel H))
    (s : ChargeLabel H →₀ ℤ)
    (ht : ∀ g, (restrict j rho).character g - (restrict j rho).dual.character g =
      TorusCharacter.eval (chiralDifference (targetWithSinglets P s)) g) :
    P.quark = P.up ∧ P.quark = P.electron ∧ P.down = P.lepton :=
  profiles_compatible c rho P s ht

example (j : Torus →* G) (p : Equiv.Perm (Fin 5)) (c : Realizes j p)
    (t : Torus) (h : H) :
    inclusion j (permute p t, h) =
      (c.element, 1) * inclusion j (t, h) * (c.element, 1)⁻¹ :=
  inclusion_conjugate c (t, h)

-- No order-two or injectivity premise is hidden in the witness structure.
-- This degenerate torus map is not a positive SM matter benchmark.
example (n : G) (p : Equiv.Perm (Fin 5)) : Realizes (1 : Torus →* G) p :=
  ⟨n, by intro t; simp⟩
end

example (q : ResolvedCharacter (ZMod 3))
    (hQU : permuteResolved (Equiv.swap (3 : Fin 5) 1) q = q)
    (hQE : permuteResolved (Equiv.swap (0 : Fin 5) 4) q = q)
    (hDL : permuteResolved (Equiv.swap (0 : Fin 5) 3) q = q) :
    quarkProfile q = upProfile q ∧ quarkProfile q = electronProfile q ∧
      downProfile q = leptonProfile q :=
  profiles_equal_of_three_invariances q hQU hQE hDL

end GUT.StructuralConjugation.Audit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Conjugation source imports UV application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``GUT.StructuralConjugation.inclusion,
    ``GUT.StructuralConjugation.restrict,
    ``GUT.StructuralConjugation.inclusion_conjugate,
    ``GUT.StructuralConjugation.character_invariant,
    ``GUT.StructuralConjugation.dual_character_invariant,
    ``GUT.StructuralConjugation.target_invariant,
    ``GUT.StructuralConjugation.coefficient_eq_of_invariant,
    ``GUT.StructuralConjugation.profiles_equal_of_three_invariances,
    ``GUT.StructuralConjugation.orbitCompatible_of_three_invariances,
    ``GUT.StructuralConjugation.profiles_compatible]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Conjugation source: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Conjugation source: import boundary and {declarations.length} strict transitive axiom checks passed"
