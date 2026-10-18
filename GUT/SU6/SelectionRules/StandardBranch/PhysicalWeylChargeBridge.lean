import GUT.SU6.Characters.PhysicalWeylMomentBridge
import GUT.SU6.SelectionRules.StandardBranch.PhysicalChargeResolvedBridge
import GUT.SU6.SelectionRules.StandardBranch.StandardWeylDualTarget

/-!
# One physical dual-index target supplies both hypercharge character rigidity and standard charge-orbit bridge

First forget residual charges to apply the odd fifth-moment obstruction.
At the resulting standard cocharacter, the injective standard-key embedding
transports the same dual target to the normalized SU(5) orbit argument.
No assumption on torsion in the Abelian charge group is needed.
-/

set_option autoImplicit false

namespace GUT.PhysicalWeylChargeBridge

noncomputable section

open PhysicalWeylMomentBridge PhysicalChargeResolvedBridge PhysicalTorusCharacterBridge
open StandardPhysicalSource StandardBranchProtonObstruction

variable {A : Type*} [AddCommGroup A]

theorem forgetCharge_chiralDifference (p : PhysicalResolvedCharacter A) :
    forgetCharge (chiralDifference p) = chiralDifference (forgetCharge p) :=
  mapDomain_chiralDifference Prod.fst (fun _ => rfl) p

theorem embedStandardCharacter_chiralDifference (p : StandardAbelianCharge.ResolvedCharacter A) :
    embedStandardCharacter (StandardWeylDualTarget.chiralDifference p) =
      chiralDifference (embedStandardCharacter p) := by
  apply mapDomain_chiralDifference standardKeyEmbedding
  intro key
  exact Prod.ext (StandardWeylDualTarget.standardExponent_neg key.1) rfl

theorem dualRestriction_of_dualResolved
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ) (m n : ℤ)
    (ht : chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets)) :
    IsDualSMRestriction source.ambientLaurentModel.poly generations
      (totalSingletMultiplicity singlets) (m : ℚ) (n : ℚ) := by
  have hi := congrArg forgetCharge ht
  simp only [forgetCharge_chiralDifference, forgetCharge_sourcePhysicalResolvedCharacter,
    forgetCharge_exactSMWithSingletsResolvedCharacter] at hi
  have hr := congrArg toRationalCharacter hi
  simpa only [IsDualSMRestriction, toRationalCharacter_chiralDifference,
    toRationalCharacter_restrictIntegralCharacter, toRationalCharacter_exactSMCharacter] using hr

theorem eq_standard_of_dualResolved
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ) (m n : ℤ)
    (hn : generations ≠ 0)
    (ht : chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets)) :
    m = -2 ∧ n = 3 := by
  have he := eq_standard_of_virtualModel_dualRestriction source.ambientLaurentModel
    generations (totalSingletMultiplicity singlets) (m : ℚ) (n : ℚ) hn
    (dualRestriction_of_dualResolved source generations charges singlets m n ht)
  exact ⟨by exact_mod_cast he.1, by exact_mod_cast he.2⟩

theorem standardDualCharacter_of_dualResolved
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ) (m n : ℤ)
    (hn : generations ≠ 0)
    (ht : chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets)) :
    StandardWeylDualTarget.chiralDifference (source.resolvedCharacter (0 : ℤ →+ A)) =
      StandardWeylDualTarget.chiralDifference
        (StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter generations charges singlets) := by
  obtain ⟨rfl, rfl⟩ := eq_standard_of_dualResolved source generations charges singlets m n hn ht
  apply embedStandardCharacter_injective
  simpa only [embedStandardCharacter_chiralDifference,
    sourcePhysicalResolvedCharacter_standard, exactSMWithSingletsResolvedCharacter_standard] using ht

theorem su5OrbitCompatible_of_dualResolved
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ) (m n : ℤ)
    (hn : generations ≠ 0)
    (ht : chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets)) :
    SU5OrbitCompatible charges :=
  StandardWeylDualTarget.su5OrbitCompatible_of_chiralDifference_target
    (source.resolvedCharacter (0 : ℤ →+ A)) (source.resolvedCharacter_isWeylInvariant _)
    generations hn charges singlets
    (standardDualCharacter_of_dualResolved source generations charges singlets m n hn ht)

theorem proton_functionals_eq_zero_of_dualResolved
    (source : FiniteChargedContinuousUnitarySource A)
    (generations : ℤ) (charges : Charges A) (singlets : A →₀ ℤ) (m n : ℤ)
    (hn : generations ≠ 0)
    (ht : chiralDifference (sourcePhysicalResolvedCharacter m n source) =
      chiralDifference (exactSMWithSingletsResolvedCharacter generations charges singlets)) :
    protonFirst charges = 0 ∧ protonSecond charges = 0 :=
  proton_functionals_eq_zero_of_su5OrbitCompatible charges
    (su5OrbitCompatible_of_dualResolved source generations charges singlets m n hn ht)

end

end GUT.PhysicalWeylChargeBridge
