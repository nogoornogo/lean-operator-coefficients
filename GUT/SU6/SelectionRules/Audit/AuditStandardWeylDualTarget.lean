import GUT.SU6.SelectionRules.StandardBranch.StandardWeylDualTarget

/-!
# Audit of the dual SM target and the standard charge-orbit bridge connection

The finite-charge examples deliberately include two-torsion. These theorems
recover only oriented SM profiles, not the entire spectrum. The mass-source
endpoint retains its explicit UV field/source identification and IR target.
-/

set_option autoImplicit false

open GUT.StandardAbelianCharge GUT.StandardSMCharacterTarget
open GUT.StandardBranchProtonObstruction GUT.StandardWeylDualTarget

example (n : ℤ) (k : Charges (ZMod 2)) (s : ZMod 2 →₀ ℤ) :
    IsPureSMChargeSpectrum
      (chiralDifference (exactSMWithSingletsResolvedCharacter n k s)) n k :=
  chiralDifference_target_isPureSMChargeSpectrum n k s

example (p : ResolvedCharacter (ZMod 2)) : chiralDifference p (0, 1) = 0 :=
  chiralDifference_apply_selfDual p (0, 1) (by decide)

example (p : ResolvedCharacter (ZMod 2)) (hp : ResolvedWeylInvariant p)
    (n : ℤ) (hn : n ≠ 0) (k : Charges (ZMod 2)) (s : ZMod 2 →₀ ℤ)
    (htarget : chiralDifference p =
      chiralDifference (exactSMWithSingletsResolvedCharacter n k s)) :
    protonFirst k = 0 ∧ protonSecond k = 0 :=
  proton_functionals_eq_zero_of_chiralDifference_target p hp n hn k s htarget

#print axioms dualCharacter_apply
#print axioms dualCharacter_dualCharacter
#print axioms chiralDifference_apply_selfDual
#print axioms chiralDifference_isWeylInvariant
#print axioms smReducedWeight_ne_neg
#print axioms exactSMWithSinglets_apply_neg_smWeight
#print axioms chiralDifference_target_chargeProfile
#print axioms chiralDifference_target_isPureSMChargeSpectrum
#print axioms chiralDifference_target_zeroWeight
#print axioms su5OrbitCompatible_of_chiralDifference_target
#print axioms proton_functionals_eq_zero_of_chiralDifference_target
#print axioms keyMonoidHom_neg
#print axioms eval_dualCharacter
#print axioms eval_chiralDifference_eq_character
#print axioms chiralDifference_eq_target_of_mass
#print axioms su5OrbitCompatible_of_mass_dual_target
#print axioms chargedSource_proton_functionals_eq_zero_of_mass_dual_target
