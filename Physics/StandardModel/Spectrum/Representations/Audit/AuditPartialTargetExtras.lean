import Physics.StandardModel.Spectrum.Representations.SMPartialTarget
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

open Math

/-! Coefficient-level controls: exotic chiral support away from the SM, and
an opposite-SM-weight contaminant. Neither is a constructed ambient model. -/

set_option autoImplicit false
namespace Physics.SMPartialTarget.AuditExtras
noncomputable section
open StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open FiniteChargeProfiles

abbrev Charge := ZMod 3
def exotic : ReducedWeight := fun _ => 10
def extra : ResolvedCharacter Charge := Finsupp.single (exotic, 0) 1

theorem exotic_ne_sm (i : Fin 15) : exotic ≠ smReducedWeight i := by revert i; decide
theorem exotic_ne_neg_sm (i : Fin 15) : exotic ≠ -smReducedWeight i := by revert i; decide
theorem neg_exotic_ne_sm (i : Fin 15) : -exotic ≠ smReducedWeight i := by revert i; decide
theorem exotic_nonzero : exotic ≠ 0 := by decide
theorem exotic_ne_neg : exotic ≠ -exotic := by decide

theorem extra_dual_vanishes (i : Fin 15) (q : Charge) :
    chiralDifference extra (smReducedWeight i, q) = 0 := by
  have hp : (exotic, (0 : Charge)) ≠ (smReducedWeight i, q) :=
    fun he => exotic_ne_sm i (congrArg Prod.fst he)
  have hn : (exotic, (0 : Charge)) ≠ -(smReducedWeight i, q) :=
    fun he => exotic_ne_neg_sm i (congrArg Prod.fst he)
  simp only [Prod.neg_mk] at hn
  simp [extra, chiralDifference, hp, hn]

theorem extra_dual_nonzero : chiralDifference extra (exotic, (0 : Charge)) = 1 := by
  have hn : (exotic, (0 : Charge)) ≠ -(exotic, (0 : Charge)) :=
    fun he => exotic_ne_neg (congrArg Prod.fst he)
  simp only [Prod.neg_mk, neg_zero] at hn
  simp [extra, chiralDifference, hn]

theorem with_extra_matches (P : Profiles Charge) :
    MatchesSM (targetWithSinglets P 0 + extra) P :=
  add_of_dual_vanishes _ _ P (of_full_target _ P 0 rfl) extra_dual_vanishes

private theorem target_off (P : Profiles Charge) (s : Charge →₀ ℤ)
    (w : ReducedWeight) (hw : ∀ i, w ≠ smReducedWeight i) (h0 : w ≠ 0) (q : Charge) :
    targetWithSinglets P s (w, q) = 0 := by
  simp [targetWithSinglets, target, hw,
    singletResolvedCharacter_apply_of_weight_ne_zero s h0]

theorem with_extra_not_full_target (P : Profiles Charge) (s : Charge →₀ ℤ) :
    chiralDifference (targetWithSinglets P 0 + extra) ≠
      chiralDifference (targetWithSinglets P s) := by
  intro he
  have hh := congrArg (fun p : ResolvedCharacter Charge => p (exotic, 0)) he
  have hpos t := target_off P t exotic exotic_ne_sm exotic_nonzero (0 : Charge)
  have hneg t := target_off P t (-exotic) neg_exotic_ne_sm (neg_ne_zero.mpr exotic_nonzero) (0 : Charge)
  have hx := extra_dual_nonzero
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply, Finsupp.add_apply] at hh hx
  simp only [Prod.neg_mk, neg_zero, hpos, hneg] at hh hx
  omega

def contaminant : ResolvedCharacter Charge := Finsupp.single (-(smReducedWeight 0, 0)) 1

theorem contaminant_vanishes_at_positive_sm (i : Fin 15) (q : Charge) :
    contaminant (smReducedWeight i, q) = 0 := by
  have hn : -(smReducedWeight 0, (0 : Charge)) ≠ (smReducedWeight i, q) :=
    fun he => smReducedWeight_ne_neg i 0 (congrArg Prod.fst he).symm
  simp only [Prod.neg_mk, neg_zero] at hn
  simp [contaminant, hn]

theorem contaminant_breaks_matching (P : Profiles Charge) :
    ¬ MatchesSM (targetWithSinglets P 0 + contaminant) P := by
  intro ht
  have he := ht 0 0
  have hp := chiralDifference_target_apply P (0 : Charge →₀ ℤ) 0 0
  have hz := contaminant_vanishes_at_positive_sm 0 0
  have hc : contaminant (-(smReducedWeight 0, (0 : Charge))) = 1 := by simp [contaminant]
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply, Finsupp.add_apply] at he hp
  rw [hz, hc] at he
  omega

end
end Physics.SMPartialTarget.AuditExtras

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Partial extras imports application {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Physics.SMPartialTarget.AuditExtras.extra_dual_vanishes,
    ``Physics.SMPartialTarget.AuditExtras.extra_dual_nonzero,
    ``Physics.SMPartialTarget.AuditExtras.with_extra_matches,
    ``Physics.SMPartialTarget.AuditExtras.with_extra_not_full_target,
    ``Physics.SMPartialTarget.AuditExtras.contaminant_vanishes_at_positive_sm,
    ``Physics.SMPartialTarget.AuditExtras.contaminant_breaks_matching]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Partial extras: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Partial extras: import boundary and {declarations.length} strict transitive axiom checks passed"
