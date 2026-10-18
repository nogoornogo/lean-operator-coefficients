import Math.LieGroups.E6.Minuscule.CompactCenter
import Math.LieGroups.E6.Minuscule.NormalizerCenter
import Math.LieGroups.E6.Audit.AuditCompactLieAlgebra

/-! # E6-0p: actual component center injects into the 27th roots, not conversely -/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule
open scoped Matrix Matrix.Norms.L2Operator

example : Finite (Subgroup.center compactIdentityComponent) := inferInstance

example : IsCyclic (Subgroup.center compactIdentityComponent) := inferInstance

example : Nat.card (Subgroup.center compactIdentityComponent) ∣ 27 := compactCenter_card_dvd

example (g : compactIdentityComponent) :
    g ∈ Subgroup.center compactIdentityComponent ↔ ∃ z : ℂ, compactMatrix g = z • 1 :=
  compact_mem_center_iff_scalar g

example (g : compactIdentityComponent) (hg : g ∈ Subgroup.center compactIdentityComponent) :
    g ^ 27 = 1 := compact_center_pow g hg

-- The ambient normalizer's negative control still does not locate its component.
example : ¬∀ g ∈ Subgroup.center compactNormalizer, g ^ (3 : ℕ) = 1 :=
  compactNormalizer_center_not_exponent_three

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.compact_center_commutes_real,
    ``Math.E6.Minuscule.compact_commutant_scalar,
    ``Math.E6.Minuscule.compact_center_scalar,
    ``Math.E6.Minuscule.compact_mem_center_iff_scalar,
    ``Math.E6.Minuscule.compactCenterScalar,
    ``Math.E6.Minuscule.compactCenterScalar_pow,
    ``Math.E6.Minuscule.compactCenterScalar_ne_zero,
    ``Math.E6.Minuscule.compactCenterScalar_injective,
    ``Math.E6.Minuscule.compactCenterRoot,
    ``Math.E6.Minuscule.compactCenterRoot_injective,
    ``Math.E6.Minuscule.compactCenter_finite,
    ``Math.E6.Minuscule.compactCenter_isCyclic,
    ``Math.E6.Minuscule.compactCenter_card_dvd,
    ``Math.E6.Minuscule.compact_center_pow]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0p: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0p: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0p: checked {declarations.length} declarations against the standard axiom allowlist"
