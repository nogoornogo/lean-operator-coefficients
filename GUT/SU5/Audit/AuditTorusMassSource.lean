import Math.Audit.ImportOrigin
import GUT.SU5.SelectionRules.TorusMassSource
import Math.RepresentationTheory.Unitary.CommutingUnitaryActions
import Physics.StandardModel.Spectrum.Charges.Audit.AuditFiniteChargeProfiles

open Physics

open Math Math.SU5

/-! CHAIN-2 source audits. Target Weyl invariance and occupied radical
vectors are conclusions. Incompatible IR charge profiles are rejected even
when they have the correct uncharged generation count. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Actual SU(5) torus source imports SU(6): {mod}"

namespace GUT.SU5.AuditTorusMassSource
open Physics.SU5

noncomputable section

open StandardModelEmbedding StandardAbelianCharge FiniteAbelianChargeSectors
open StandardSMCharacterTarget FiniteChargeProfiles InvariantWeylMass
open StandardWeylDualTarget
open TorusCharacter TorusCharacterSource TorusMassSource AuditFiniteChargeProfiles

theorem raw_weights_not_faithful :
    (fun _ : Fin 5 => (0 : ℤ)) ≠ (fun _ : Fin 5 => (1 : ℤ)) ∧
      rawCharacter (fun _ => 0) = rawCharacter (fun _ => 1) := by
  constructor
  · intro he
    have hh := congrFun he 0
    norm_num at hh
  · ext z
    simp [rawCharacter]

theorem odd_weyl_representative (z : MaximalTorus.Torus) :
    MaximalTorus.hom (MaximalTorus.permute (Equiv.swap 3 1) z) =
      MonomialElements.signedPermutation (Equiv.swap 3 1) * MaximalTorus.hom z *
        (MonomialElements.signedPermutation (Equiv.swap 3 1))⁻¹ :=
  MaximalTorus.hom_conjugate _ _

theorem finite_labels_not_identified (n : ℕ) [NeZero n] (w : ReducedWeight)
    (r s : ZMod n) (hrs : r ≠ s) :
    keyCharacter (w, cyclicLabels n r) ≠ keyCharacter (w, cyclicLabels n s) := by
  intro he
  apply hrs
  exact cyclicLabels_injective n (congrArg Prod.snd (keyCharacter_injective he))

/-- Order two does not merge a nonzero SM weight with its dual: only the
residual charge is self-dual. -/
theorem order_two_sm_dual_distinct (i : Fin 15) :
    keyCharacter (smReducedWeight i, cyclicLabels 2 1) ≠
      AbelianActualSpectrum.dualCharacter (keyCharacter (smReducedWeight i, cyclicLabels 2 1)) := by
  rw [keyCharacter_neg]
  intro he
  exact smReducedWeight_ne_neg i i (congrArg Prod.fst (keyCharacter_injective he))

variable {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ (TargetGroup × H) E)
  (B : SymmetricMass (restrict rho))

theorem incompatible_target_impossible (q : ChargeLabel H) (hq : q ≠ 0)
    (s : ChargeLabel H →₀ ℤ) :
    ¬ HasTarget rho B (incompatibleFamily q).profiles s := by
  intro ht
  exact incompatible_not_orbitCompatible q hq (profiles_compatible rho B _ s ht)

theorem order_three_target_impossible
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (r : Representation ℂ (TargetGroup × Multiplicative (ZMod 3)) V)
    (M : SymmetricMass (restrict r)) (s : ChargeLabel (Multiplicative (ZMod 3)) →₀ ℤ) :
    ¬ HasTarget r M (incompatibleFamily (cyclicLabels 3 1)).profiles s :=
  incompatible_target_impossible r M _ order_three_character.1 s

#print axioms MaximalTorus.hom_injective
#print axioms MaximalTorus.hom_conjugate
#print axioms TorusCharacter.weightCharacter_normalize
#print axioms TorusCharacter.weightCharacter_injective
#print axioms TorusCharacter.keyCharacter_injective
#print axioms TorusCharacter.eval_injective
#print axioms TorusCharacter.eval_permute
#print axioms TorusCharacter.keyCharacter_neg
#print axioms PhysicalTorus.toTorus_surjective
#print axioms PhysicalTorus.weightCharacter_toTorus
#print axioms PhysicalTorus.weightCharacter_fourier
#print axioms PhysicalTorus.hom_gaugePoint
#print axioms PhysicalTorus.eval_physical_iff
#print axioms TorusCharacterSource.character_invariant
#print axioms TorusCharacterSource.dual_character_invariant
#print axioms TorusCharacterSource.target_invariant
#print axioms FiniteChargeProfiles.orbitCompatible_of_dual_invariant
#print axioms TorusMassSource.hasTarget_iff_physical
#print axioms TorusMassSource.source_target
#print axioms TorusMassSource.profiles_compatible
#print axioms TorusMassSource.spectrum_nonneg
#print axioms TorusMassSource.chiral_spectrum
#print axioms TorusMassSource.exists_zeroMode
#print axioms TorusMassSource.exists_actual_signature_pair
#print axioms TorusMassSource.selection_rule_obstruction
#print axioms CommutingUnitaryActions.combined_unitary
#print axioms CommutingUnitaryActions.combined_restrict_left
#print axioms CommutingUnitaryActions.combined_restrict_right
#print axioms raw_weights_not_faithful
#print axioms odd_weyl_representative
#print axioms finite_labels_not_identified
#print axioms order_two_sm_dual_distinct
#print axioms incompatible_target_impossible
#print axioms order_three_target_impossible

end

end GUT.SU5.AuditTorusMassSource
