import Math.RepresentationTheory.Decomposition.FiniteConstituentSupport

/-! Complete finite coupling tests retain nonsinglets of both tensor factors.
Equivalence to the dual of a block, rather than separate singlet support, is
the criterion. All decompositions are actual equivariant direct sums. -/
namespace Math.FiniteTensorConstituentSupport
set_option autoImplicit false
noncomputable section
open Representation FiniteSemisimpleDecomposition

variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (rho : Representation ℂ G V) (sigma : Representation ℂ G W)

def turn : IntertwiningMap rho sigma.dual ≃ₗ[ℂ] IntertwiningMap sigma rho.dual :=
  (InvariantTensorCurry.equiv rho sigma).symm.trans
    ((InvariantCoefficientTransport.alongEquiv (Representation.TensorProduct.comm rho sigma)).trans
      (InvariantTensorCurry.equiv sigma rho))

variable {rho sigma}
  (D : Decomposition rho) (E : Decomposition sigma)

def coefficientEquiv : InvariantCoefficientTransport.Invariants (rho.tprod sigma) ≃ₗ[ℂ]
    (∀ i, ∀ j, IntertwiningMap (E.blockRepresentation j) (D.blockRepresentation i).dual) :=
  (InvariantTensorCurry.equiv rho sigma).trans
    ((FiniteConstituentSupport.homEquiv D sigma.dual).trans
      (LinearEquiv.piCongrRight (fun i => (turn (D.blockRepresentation i) sigma).trans
        (FiniteConstituentSupport.homEquiv E (D.blockRepresentation i).dual))))

theorem allowed_iff [FiniteDimensional ℂ V] :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (rho.tprod sigma)) ↔
      ∃ i, ∃ j, Nonempty (Representation.Equiv
        (E.blockRepresentation j) (D.blockRepresentation i).dual) := by
  have he := SelectionCriteria.allowed_equiv (coefficientEquiv D E)
  rw [SelectionCriteria.allowed_family] at he
  refine he.trans (exists_congr (fun i => ?_))
  let : FiniteDimensional ℂ (D.block i) := FiniteDimensional.of_injective
    ((D.block i).subtype.restrictScalars ℂ) (D.block i).subtype_injective
  let := D.blockRepresentation_isIrreducible i
  let := RepresentationTheory.dual_isIrreducible (D.blockRepresentation i)
  have hb := FiniteConstituentSupport.irreducible_target_iff E (D.blockRepresentation i).dual
  exact (SelectionCriteria.allowed_equiv (FiniteConstituentSupport.homEquiv E
    (D.blockRepresentation i).dual)).symm.trans hb

theorem forbidden_iff [FiniteDimensional ℂ V] :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (rho.tprod sigma)) ↔
      ∀ i j, ¬ Nonempty (Representation.Equiv
        (E.blockRepresentation j) (D.blockRepresentation i).dual) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, allowed_iff D E]
  simp only [not_exists]

end
end Math.FiniteTensorConstituentSupport
