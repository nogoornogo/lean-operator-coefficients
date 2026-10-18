import Math.RepresentationTheory.SU3ColorTensorWord
import Math.RepresentationTheory.SU3ExteriorColorWord
import Math.RepresentationTheory.SU3ColorPositive
import Math.RepresentationTheory.ExternalCoefficientSupport
import Math.RepresentationTheory.SU2PairExterior

/-! Simultaneous positive color/weak/spin coupling conditions in proved
families. All factors are assembled before the independent group actions
are separated; nonsinglet intermediate factors are retained. -/
namespace Math.SU3CompatibleCoupling
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor InvariantCoefficientTransport
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
@[reducible] local instance (a b : ℕ) : AddCommGroup (SU2PairExterior.PairCarrier a b) := inferInstance

abbrev SpinCarrier (a b c d : ℕ) := SU2PairExterior.PairCarrier a b ⊗[ℂ] SU2PairExterior.PairCarrier c d
@[reducible] local instance (a b c d : ℕ) : AddCommGroup (SpinCarrier a b c d) := inferInstance
abbrev spinPair (a b c d : ℕ) : Representation ℂ (WeakDoubletScalars.Group × WeakDoubletScalars.Group)
    (SpinCarrier a b c d) := (SU2PairExterior.pair a b).tprod (SU2PairExterior.pair c d)

theorem spin_iff (a b c d : ℕ) : SelectionCriteria.Allowed (Invariants (spinPair a b c d)) ↔ a=c ∧ b=d :=
  (SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv (SU2PairExterior.pair a b)
    (SU2PairExterior.pair c d))).trans
      ((SelectionCriteria.allowed_equiv (CompactCoefficientSupport.homEquiv
        (.refl (SU2PairExterior.pair a b)) (SU2PairExterior.pairSelfDual c d).symm)).trans
          (SU2PairExterior.pair_hom_iff a b c d))

/-- Closed iff for an arbitrary ordered defining/dual color word and two
joint SU2 target labels; both nonsinglet labels must match simultaneously. -/
theorem word_iff (w : SU3ColorTensorWord.Word) (a b c d : ℕ) :
    SelectionCriteria.Allowed (Invariants (external (SU3ColorTensorWord.action w) (spinPair a b c d))) ↔
      SU3ColorTensorWord.positiveCount w%3=SU3ColorTensorWord.negativeCount w%3 ∧ a=c ∧ b=d := by
  rw [ExternalCoefficientSupport.allowed_iff,SU3ColorTensorWord.allowed_iff,spin_iff]

/-- Exterior restrictions are resolved before the joint weak/spin matching
test. This applies to arbitrary ordered words and arbitrary exterior degrees. -/
theorem exterior_word_iff (w : SU3ExteriorColorWord.Word) (a b c d : ℕ) :
    SelectionCriteria.Allowed (Invariants
      (external (SU3ExteriorColorWord.action w) (spinPair a b c d))) ↔
      (SU3ExteriorColorWord.Fits w ∧
        SU3ColorTensorWord.positiveCount (SU3ExteriorColorWord.reduced w)%3=
          SU3ColorTensorWord.negativeCount (SU3ExteriorColorWord.reduced w)%3) ∧ a=c ∧ b=d := by
  rw [ExternalCoefficientSupport.allowed_iff,SU3ExteriorColorWord.allowed_iff,spin_iff]

/-- An actual symmetric-color/dual-color pair, including the square
branches, coupled with independent weak and spin labels. -/
theorem symmetric_iff (m a b c d : ℕ) : SelectionCriteria.Allowed
    (Invariants (external (SU3ColorPositive.symmetricPair m) (spinPair a b c d))) ↔ a=c ∧ b=d := by
  rw [ExternalCoefficientSupport.allowed_iff,spin_iff]
  exact and_iff_right (SU3ColorPositive.symmetric_allowed m)

/-- The actual trace-free color branches admit this positive paired
coupling; their irreducibility is not a hypothesis. -/
theorem adjoint_iff (a b c d : ℕ) : SelectionCriteria.Allowed
    (Invariants (external SU3ColorPositive.adjointPair (spinPair a b c d))) ↔ a=c ∧ b=d := by
  rw [ExternalCoefficientSupport.allowed_iff,spin_iff]
  exact and_iff_right SU3ColorPositive.adjoint_allowed

theorem dual_adjoint_iff (a b c d : ℕ) : SelectionCriteria.Allowed
    (Invariants (external SU3ColorPositive.dualAdjointPair (spinPair a b c d))) ↔ a=c ∧ b=d := by
  rw [ExternalCoefficientSupport.allowed_iff,spin_iff]
  exact and_iff_right SU3ColorPositive.dual_adjoint_allowed

end
end Math.SU3CompatibleCoupling
