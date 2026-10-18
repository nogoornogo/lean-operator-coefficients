import GUT.Sp.RestrictedCharacter
import Physics.StandardModel.Spectrum.SelfDualChirality

open Math

/-! The positive exact SM dual target is impossible for any subgroup
restriction of an actual compact symplectic source. The specified faithful
target evaluator remains explicit; no SU(5) chain is required. -/

set_option autoImplicit false

namespace GUT.CompactSymplectic

open Math.CompactSymplectic
noncomputable section

open SelfDualChirality StandardAbelianCharge StandardSMCharacterTarget StandardWeylDualTarget
open FiniteChargeProfiles InvariantWeylMass

theorem no_positive_SM_target {n : ℕ} {K T V A : Type*} [_root_.Group K] [CommGroup T]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup A]
    (rho : Representation ℂ (Group n) V) (i : K →* Group n)
    (B : SymmetricMass (rho.comp i)) (test : T →* K)
    (weight : ReducedWeight → (T →* ℂ)) (hw : Function.Injective weight)
    (F : Family A) (s : A →₀ ℤ) :
    ¬ ∀ t, B.radical.toRepresentation.character (test t) -
      B.radical.toRepresentation.dual.character (test t) =
        evaluateGauge weight
          (forgetCharges (chiralDifference (targetWithSinglets F.profiles s))) t :=
  not_has_target_of_zero_source (rho.comp i) B test weight hw F s
    (fun t => restricted_character_eq_dual rho i (test t))

end

end GUT.CompactSymplectic
