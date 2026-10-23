import GUT.SU6.SelectionRules.StandardBranch.WeylZeroModeSupport

open Physics

/-!
# Explicitly conjugated operators for negative generation index

Conjugation reverses gauge and residual labels, and the residual character
of the whole operator is inverted. These are conjugate signatures, not
positive-baryon-number operators relabelled as if their orientation agreed.
-/

set_option autoImplicit false

namespace GUT.WeylConjugateOperator

noncomputable section

open StandardAbelianCharge StandardSMCharacterTarget StandardWeylMassSource
open StandardWeylDualTarget StandardModelLocalOperator StandardBranchProtonObstruction
open WeylZeroModeSupport

variable {H : Type*} [CommGroup H]

/-- Support is tested at the actual conjugate keys `(-w,-q)` in p. -/
structure SupportedConjugateInvariantOperator (p : ResolvedCharacter (ChargeLabel H)) where
  charges : Charges (ChargeLabel H)
  supported : ChargesSupported (dualCharacter p) charges
  operator : StandardOperatorClass
  invariant : (operator.residualCharacter charges)⁻¹ = 1

/-- Signed baryon number of the explicitly conjugated signature. -/
def conjugateThreeB (O : StandardOperatorClass) : ℤ :=
  -(quantumNumbers O.operator).threeB

theorem conjugateThreeB_eq (O : StandardOperatorClass) : conjugateThreeB O = -3 := by
  have h := O.isPhysicalDeltaBOneOperator.2.2.1
  simp [conjugateThreeB, h]

theorem conjugateChargesSupported (M : StandardWeylModel H) (hn : M.generations < 0) :
    ChargesSupported (dualCharacter (lightSpectrum M)) M.charges := by
  have hp := chiralDifference_target_isPureSMChargeSpectrum
    M.generations M.charges M.singlets
  rw [← lightSpectrum_chiralDifference M] at hp
  have hs (w : ReducedWeight) (q : ChargeLabel H)
      (he : chargeProfile (chiralDifference (lightSpectrum M)) w =
        Finsupp.single q M.generations) :
      chargeProfile (dualCharacter (lightSpectrum M)) w q ≠ 0 := by
    have h := congrArg (fun f => f q) he
    simp only [chargeProfile_apply, chiralDifference, Finsupp.sub_apply,
      dualCharacter_apply, Finsupp.single_eq_same] at h
    have hp := lightSpectrum_nonneg M (w, q)
    simp only [chargeProfile_apply, dualCharacter_apply]
    omega
  exact ⟨hs _ _ hp.quark, hs _ _ hp.up, hs _ _ hp.down,
    hs _ _ hp.lepton, hs _ _ hp.electron⟩

def conjugateQque (M : StandardWeylModel H) (hn : M.generations < 0) :
    SupportedConjugateInvariantOperator (lightSpectrum M) where
  charges := M.charges
  supported := conjugateChargesSupported M hn
  operator := .qque
  invariant := by simp [StandardWeylSupportedOperator.protonFirstCharacter_eq_one M]

def conjugateDuql (M : StandardWeylModel H) (hn : M.generations < 0) :
    SupportedConjugateInvariantOperator (lightSpectrum M) where
  charges := M.charges
  supported := conjugateChargesSupported M hn
  operator := .duql
  invariant := by simp [StandardWeylSupportedOperator.protonSecondCharacter_eq_one M]

/-- Neither orientation is silently identified with the other. -/
theorem exists_invariant_operator_or_conjugate (M : StandardWeylModel H) :
    Nonempty (SupportedInvariantOperator (lightSpectrum M)) ∨
      Nonempty (SupportedConjugateInvariantOperator (lightSpectrum M)) := by
  rcases lt_or_gt_of_ne M.generations_ne with hn | hn
  · exact Or.inr ⟨conjugateQque M hn⟩
  · exact Or.inl ⟨WeylZeroModeSupport.supportedQque M hn⟩

def ForbidsBothOrientations (p : ResolvedCharacter (ChargeLabel H)) : Prop :=
  ForbidsEverySupportedStandardOperator p ∧
    ∀ k : Charges (ChargeLabel H), ChargesSupported (dualCharacter p) k →
      ∀ O : StandardOperatorClass, (O.residualCharacter k)⁻¹ ≠ 1

theorem not_forbidsBothOrientations (M : StandardWeylModel H) :
    ¬ ForbidsBothOrientations (lightSpectrum M) := by
  rintro ⟨hpos, hneg⟩
  rcases exists_invariant_operator_or_conjugate M with h | h
  · obtain ⟨w⟩ := h
    exact w.not_forbidsEverySupportedStandardOperator hpos
  · obtain ⟨w⟩ := h
    exact hneg w.charges w.supported w.operator w.invariant

end

end GUT.WeylConjugateOperator
