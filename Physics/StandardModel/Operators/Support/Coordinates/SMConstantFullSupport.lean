import Physics.StandardModel.Operators.Support.Quark.SMQConjugateKernel

/-! Unreduced derivative-free Higgs support for the fixed three-flavor
constant Q/L families with trivial residual group. -/
namespace Physics.SMConstantFullSupport
set_option autoImplicit false
noncomputable section
open Math Representation

abbrev flavor := LLHHKernelRank.flavor

theorem local_surjective : Function.Surjective
    (MonoidHom.inl SMIntegralLocalWeights.Group Unit) := by
  rintro ⟨g,h⟩
  exact ⟨g, Prod.ext rfl (Subsingleton.elim _ _)⟩

variable {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def testEquiv (m : ℕ) (delta : ℤ) : SMFiniteHiggsSupport.Test flavor p m delta ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta) :=
  (InvariantCoefficientTransport.alongSurjection (SMWeylFiniteKernel.fullAction flavor p m delta)
    (MonoidHom.inl SMIntegralLocalWeights.Group Unit) local_surjective).symm.trans
      (InvariantCoefficientTransport.alongEquiv
        (BnvLocalConjugation.tensorPullback (SMFiniteHiggsSupport.source flavor p)
          (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := Unit))
            SMHiggsConstituents.character m delta) (MonoidHom.inl SMIntegralLocalWeights.Group Unit)).symm)

variable (n : ℕ)

theorem quark_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace flavor (SMQExactCoordinates.pattern n) h d) ↔
    ∃ m : Fin (SMContentWeakBound.bound (SMQExactCoordinates.pattern n)+1),
      BoundedHiggsSupport.Admissible h d m.val ∧
        (SMQGaussianKernel.polynomial n m.val ((h : ℤ)-d)).coeff 0 = 0 := by
  rw [SMFiniteHiggsSupport.original_allowed_iff]
  apply exists_congr
  intro m
  exact and_congr_right (fun _ => (SelectionCriteria.allowed_equiv
    (testEquiv (SMQExactCoordinates.pattern n) m.val ((h : ℤ)-d))).trans
      (SMQGaussianKernel.allowed_iff flavor n m.val ((h : ℤ)-d)))

theorem conjugate_quark_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace flavor (SMConstantContentRanks.pattern 5 n) h d) ↔
    ∃ m : Fin (SMContentWeakBound.bound (SMConstantContentRanks.pattern 5 n)+1),
      BoundedHiggsSupport.Admissible h d m.val ∧
        (SMQGaussianKernel.polynomial n m.val (-((h : ℤ)-d))).coeff 0 = 0 := by
  rw [SMFiniteHiggsSupport.original_allowed_iff]
  apply exists_congr
  intro m
  exact and_congr_right (fun _ => (SelectionCriteria.allowed_equiv
    (testEquiv (SMConstantContentRanks.pattern 5 n) m.val ((h : ℤ)-d))).trans
      (SMQConjugateKernel.allowed_iff flavor n m.val ((h : ℤ)-d)))

theorem lepton_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace flavor (SMLCompactWeyl.pattern n) h d) ↔
    ∃ m : Fin (SMContentWeakBound.bound (SMLCompactWeyl.pattern n)+1),
      BoundedHiggsSupport.Admissible h d m.val ∧
        ((h : ℤ)-d = n ∧ SMLKernelDimension.multiplicity n m.val ≠ 0) := by
  rw [SMFiniteHiggsSupport.original_allowed_iff]
  apply exists_congr
  intro m
  exact and_congr_right (fun _ => (SelectionCriteria.allowed_equiv
    (testEquiv (SMLCompactWeyl.pattern n) m.val ((h : ℤ)-d))).trans
      (SMLKernelDimension.allowed_iff flavor n m.val ((h : ℤ)-d)))

theorem conjugate_lepton_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace flavor (SMConstantContentRanks.pattern 8 n) h d) ↔
    ∃ m : Fin (SMContentWeakBound.bound (SMConstantContentRanks.pattern 8 n)+1),
      BoundedHiggsSupport.Admissible h d m.val ∧
        ((h : ℤ)-d = -(n : ℤ) ∧ SMLKernelDimension.multiplicity n m.val ≠ 0) := by
  rw [SMFiniteHiggsSupport.original_allowed_iff]
  apply exists_congr
  intro m
  exact and_congr_right (fun _ => (SelectionCriteria.allowed_equiv
    (testEquiv (SMConstantContentRanks.pattern 8 n) m.val ((h : ℤ)-d))).trans
      (SMLConjugateMultiplicity.allowed_iff flavor n m.val ((h : ℤ)-d)))

end
end Physics.SMConstantFullSupport
