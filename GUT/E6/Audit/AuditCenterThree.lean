import GUT.E6.Minuscule.CentralQuotientObstruction
import Lean.Util.CollectAxioms

open Math

/-! The actual connected candidate contains a central element of order
three, and its defining 27 cannot descend to the center quotient. These
checks do not assert an exact center or simply connected global form. -/

set_option autoImplicit false

namespace GUT.E6.Audit

open Math.E6
noncomputable section

open Minuscule
open scoped Matrix Matrix.Norms.L2Operator

example : compactMatrix centralScalar3 = scalarRoot3 • (1 : Matrix27) :=
  centralScalar3_matrix

example : centralScalar3 ∈ Subgroup.center compactIdentityComponent ∧
    orderOf centralScalar3 = 3 := ⟨centralScalar3_mem_center, centralScalar3_orderOf⟩

example : centralScalar27 ^ 9 ∈ compactIdentityComponent := centralScalar27_pow_nine_mem

example : 3 ∣ Nat.card (Subgroup.center compactIdentityComponent) ∧
    Nat.card (Subgroup.center compactIdentityComponent) ∣ 27 := compactCenter_card_bounds

-- These divisibility bounds alone do not force the center to have order three.
example : ∃ n : ℕ, 3 ∣ n ∧ n ∣ 27 ∧ n ≠ 3 := ⟨9, by decide, by decide, by decide⟩

example : ¬ ∃ rho : Representation ℂ (compactIdentityComponent ⧸
    Subgroup.center compactIdentityComponent) Hilbert27,
    representation = rho.comp (QuotientGroup.mk' (Subgroup.center compactIdentityComponent)) :=
  representation_not_descends_center

example : representation centralScalar3 ≠ 1 := representation_centralScalar3_ne_one

example (G : Type*) [Group G] (hG : Subgroup.center G = ⊥) :
    ¬ Nonempty (compactIdentityComponent ≃* G) := compactCandidate_not_equiv_centerless G hG

-- The full normalizer still has a different center obstruction.
example : ¬∀ g ∈ Subgroup.center compactNormalizer, g ^ (3 : ℕ) = 1 :=
  compactNormalizer_center_not_exponent_three

end

end GUT.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.gradingDirection_matrix,
    ``Math.E6.Minuscule.centerThirdDirection_matrix,
    ``Math.E6.Minuscule.scalarRoot3_primitive,
    ``Math.E6.Minuscule.scalarRoot3_ne_one,
    ``Math.E6.Minuscule.exp_graded_entry,
    ``Math.E6.Minuscule.exp_centerThirdDirection,
    ``Math.E6.Minuscule.centralScalar3,
    ``Math.E6.Minuscule.centralScalar3_matrix,
    ``Math.E6.Minuscule.centralScalar3_mem_center,
    ``Math.E6.Minuscule.centralScalar3_pow_matrix,
    ``Math.E6.Minuscule.centralScalar3_pow_eq_one_iff,
    ``Math.E6.Minuscule.centralScalar3_orderOf,
    ``Math.E6.Minuscule.centerElement3_orderOf,
    ``Math.E6.Minuscule.three_dvd_compactCenter_card,
    ``Math.E6.Minuscule.compactCenter_card_bounds,
    ``Math.E6.Minuscule.scalarRoot27_pow_nine,
    ``Math.E6.Minuscule.centralScalar3_val,
    ``Math.E6.Minuscule.centralScalar27_pow_nine_mem,
    ``GUT.E6.Minuscule.representation_centralScalar3,
    ``GUT.E6.Minuscule.representation_centralScalar3_ne_one,
    ``GUT.E6.Minuscule.character_centralScalar3,
    ``GUT.E6.Minuscule.centralScalar3_ne_one,
    ``GUT.E6.Minuscule.compact_center_ne_bot,
    ``GUT.E6.Minuscule.representation_not_descends_center,
    ``GUT.E6.Minuscule.compactCandidate_not_equiv_centerless]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6 center three: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6 center three: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6 center three: checked {declarations.length} declarations"
