import Math.RepresentationTheory.SU2.SU2FiniteBranching
import Math.RepresentationTheory.Decomposition.FiniteTensorConstituentSupport
import Math.RepresentationTheory.SU2.SU2DoubletDuality

/-! Exact weak coupling for complete bounded SU2 sums: equal labels can pair,
including all nonsinglets. The other group factors must be treated separately. -/
namespace Math.SU2FiniteCoupling
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars SU2FiniteBranching

def selfDual (m : ℕ) : Representation.Equiv (doublet.symmetricPower m)
    (doublet.symmetricPower m).dual :=
  (duality m).trans (SplitRepresentationProjection.dualEquiv
    (SU2DoubletDuality.equivalence.symmetricPower m)).symm

variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ TauCeti.SU2 V} {sigma : Representation ℂ TauCeti.SU2 W}
  {N M : ℕ} (C : Certificate rho N) (D : Certificate sigma M)

theorem block_match_iff (i : Fin C.decomposition.numberOfBlocks)
    (j : Fin D.decomposition.numberOfBlocks) :
    Nonempty (Representation.Equiv (D.decomposition.blockRepresentation j)
      (C.decomposition.blockRepresentation i).dual) ↔
      (C.degree i).val = (D.degree j).val := by
  constructor
  · rintro ⟨e⟩
    have he : Nonempty (Representation.Equiv
        (doublet.symmetricPower (D.degree j).val) (doublet.symmetricPower (C.degree i).val)) :=
      ⟨(D.blockEquiv j).trans (e.trans
        ((SplitRepresentationProjection.dualEquiv (C.blockEquiv i)).symm.trans
          (selfDual (C.degree i).val).symm))⟩
    simp only [symmetricPower_eq] at he
    exact ((TauCeti.SU2.nonempty_equiv_symPower_iff
      (D.degree j).val (C.degree i).val).mp he).symm
  · intro h
    have e : Representation.Equiv (doublet.symmetricPower (D.degree j).val)
        (doublet.symmetricPower (C.degree i).val) := by
      rw [h]
      exact .refl _
    exact ⟨(D.blockEquiv j).symm.trans (e.trans
      ((selfDual (C.degree i).val).trans (SplitRepresentationProjection.dualEquiv (C.blockEquiv i))))⟩

theorem tensor_allowed_iff [FiniteDimensional ℂ V] :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (rho.tprod sigma)) ↔
      ∃ i, ∃ j, (C.degree i).val = (D.degree j).val :=
  (FiniteTensorConstituentSupport.allowed_iff C.decomposition D.decomposition).trans
    (exists_congr (fun i => exists_congr (fun j => block_match_iff C D i j)))

theorem tensor_forbidden_iff [FiniteDimensional ℂ V] :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (rho.tprod sigma)) ↔
      ∀ i j, (C.degree i).val ≠ (D.degree j).val := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, tensor_allowed_iff C D]
  simp only [not_exists]

end
end Math.SU2FiniteCoupling
