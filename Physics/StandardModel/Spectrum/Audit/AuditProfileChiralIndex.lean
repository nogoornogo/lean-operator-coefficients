import Math.Audit.ImportOrigin
import Physics.StandardModel.Spectrum.ProfileChiralIndex
import Physics.StandardModel.Spectrum.Audit.AuditFiniteChargeProfiles

open Math

/-! Persistent torsion, vectorlike-pair, and wrong-orientation controls. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Profile dual-index core imports SU(6): {mod}"

namespace GUT.AuditProfileChiralIndex

noncomputable section

open FiniteChargeProfiles StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open AuditFiniteChargeProfiles FiniteAbelianChargeSectors

abbrev Label := FiniteAbelianChargeSectors.ChargeLabel (Multiplicative (ZMod 2))

theorem torsion_target_coefficient (s : Label →₀ ℤ) :
    chiralDifference (targetWithSinglets (mixedFamily (cyclicLabels 2 1)).profiles s)
      (smReducedWeight 0, cyclicLabels 2 1) = 1 := by
  rw [chiralDifference_target_apply]
  exact_mod_cast (mixed_distinct_occupied _ order_two_character.1).2.1

theorem vectorlike_pairs_preserve_target (P : Profiles Label) (s : Label →₀ ℤ)
    (r : ResolvedCharacter Label) :
    chiralDifference (targetWithSinglets P s + (r + dualCharacter r)) =
      chiralDifference (targetWithSinglets P s) := chiralDifference_add_vectorlike _ _

theorem torsion_singlet_invisible (n : ℤ) :
    chiralDifference (Finsupp.single ((0 : ReducedWeight), cyclicLabels 2 1) n) = 0 := by
  have hq : -cyclicLabels 2 1 = cyclicLabels 2 1 := by
    rw [← map_neg, show -(1 : ZMod 2) = 1 by decide]
  have hkey : -((0 : ReducedWeight), cyclicLabels 2 1) = (0, cyclicLabels 2 1) := by
    simp [hq]
  rw [chiralDifference, dualCharacter, Finsupp.mapDomain_single, hkey, sub_self]

/-- Nonzero signed dual support may select only the opposite orientation. -/
theorem wrong_orientation_control :
    let key : ResolvedKey Label := (smReducedWeight 0, cyclicLabels 2 1)
    let p : ResolvedCharacter Label := Finsupp.single (-key) 1
    chiralDifference p key = -1 ∧ p key = 0 := by
  classical
  dsimp only
  have hn : -(smReducedWeight 0, cyclicLabels 2 1) ≠ (smReducedWeight 0, cyclicLabels 2 1) := by
    intro h
    exact smReducedWeight_ne_neg 0 0 (congrArg Prod.fst h).symm
  simp only [chiralDifference, Finsupp.sub_apply, dualCharacter_apply,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne' hn]
  norm_num

#print axioms targetWithSinglets_apply_neg_smWeight
#print axioms chiralDifference_target_apply
#print axioms orbitCompatible_of_dual_target
#print axioms coefficient_lower_bound
#print axioms coefficient_pos
#print axioms chargesSupported_of_occupied
#print axioms chiralDifference_add_vectorlike
#print axioms torsion_target_coefficient
#print axioms vectorlike_pairs_preserve_target
#print axioms torsion_singlet_invisible
#print axioms wrong_orientation_control

end

end GUT.AuditProfileChiralIndex
