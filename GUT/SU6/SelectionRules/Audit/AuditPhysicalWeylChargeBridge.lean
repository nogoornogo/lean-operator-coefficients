import GUT.SU6.SelectionRules.StandardBranch.PhysicalWeylChargeBridge

/-! Persistent audit of the odd-moment and charge-resolved dual-index route. -/

set_option autoImplicit false

namespace GUT.AuditPhysicalWeylChargeBridge

open PhysicalWeylMomentBridge PhysicalWeylChargeBridge PhysicalChargeResolvedBridge
open StandardBranchProtonObstruction

example (source : StandardPhysicalSource.FiniteChargedContinuousUnitarySource (ZMod 2))
    (generations : ℤ) (charges : Charges (ZMod 2)) (singlets : ZMod 2 →₀ ℤ) (m n : ℤ)
    (hn : generations ≠ 0)
    (ht : chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets)) :
    (m = -2 ∧ n = 3) ∧ (protonFirst charges = 0 ∧ protonSecond charges = 0) :=
  ⟨eq_standard_of_dualResolved source generations charges singlets m n hn ht,
    proton_functionals_eq_zero_of_dualResolved source generations charges singlets m n hn ht⟩

/-- Losing a self-dual sector is not reversed anywhere in the bridge. -/
example : chiralDifference
    (Finsupp.single (0 : PhysicalFifthMomentBridge.PhysicalWeight) 1) = 0 := by
  simp [chiralDifference, dual]

example : (Finsupp.single (0 : PhysicalFifthMomentBridge.PhysicalWeight) 1 :
    PhysicalFifthMomentBridge.PhysicalCharacter) ≠ 0 := by simp

#print axioms fifthMomentValue_dual
#print axioms fifthMomentValue_chiralDifference
#print axioms hasSMFifthMoment_of_dualRestriction
#print axioms dualRestriction_of_characterOnPhysicalTorus
#print axioms eq_standard_of_continuousUnitarySource_dualCharacterOnPhysicalTorus
#print axioms dualRestriction_of_dualResolved
#print axioms eq_standard_of_dualResolved
#print axioms standardDualCharacter_of_dualResolved
#print axioms su5OrbitCompatible_of_dualResolved
#print axioms proton_functionals_eq_zero_of_dualResolved

end GUT.AuditPhysicalWeylChargeBridge
