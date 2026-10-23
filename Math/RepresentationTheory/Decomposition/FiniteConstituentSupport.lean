import Math.RepresentationTheory.Decomposition.FiniteSemisimpleDecomposition
import Math.RepresentationTheory.Decomposition.FiniteIrreducibleQuotient
import Math.RepresentationTheory.Decomposition.IrreducibilityTransport
import Math.RepresentationTheory.Constructions.DirectSumResidualHom
import Math.RepresentationTheory.Decomposition.FiniteBlockHom
import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Finite constituent support without evaluating a character or a dimension.
The decomposition is an actual equivariant direct sum; its blocks may repeat.
The remaining equivalence tests are propositions, not a decision procedure. -/
namespace Math.FiniteConstituentSupport
set_option autoImplicit false
noncomputable section
open Representation FiniteSemisimpleDecomposition
open scoped MonoidAlgebra TensorProduct

variable {G V W : Type*} [Group G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {rho : Representation ℂ G V} (D : Decomposition rho)

/-- A finite direct sum, represented as a product without changing the action. -/
def piEquiv : Representation.Equiv rho (FiniteBlockHom.action D.blockRepresentation) :=
  D.representationEquivDirectSum.trans
    { toLinearEquiv := DFinsupp.linearEquivFunOnFintype
      isIntertwining' g := by ext x i; rfl }

def homEquiv (sigma : Representation ℂ G W) :
    IntertwiningMap rho sigma ≃ₗ[ℂ]
      (∀ i, IntertwiningMap (D.blockRepresentation i) sigma) :=
  DirectSumResidualHom.coefficientEquiv D.blockRepresentation sigma
    D.representationEquivDirectSum.symm

theorem hom_allowed_iff (sigma : Representation ℂ G W) :
    SelectionCriteria.Allowed (IntertwiningMap rho sigma) ↔
      ∃ i, SelectionCriteria.Allowed (IntertwiningMap (D.blockRepresentation i) sigma) :=
  (SelectionCriteria.allowed_equiv (homEquiv D sigma)).trans
    (SelectionCriteria.allowed_family _)

/-- For an irreducible target, a nonzero block map is precisely an equivalence.
No positivity or branching certificate is assumed beyond the actual sum. -/
theorem irreducible_target_iff (sigma : Representation ℂ G W)
    [IsIrreducible sigma] :
    SelectionCriteria.Allowed (IntertwiningMap rho sigma) ↔
      ∃ i, Nonempty (Representation.Equiv (D.blockRepresentation i) sigma) := by
  rw [hom_allowed_iff D sigma]
  apply exists_congr
  intro i
  let := D.blockRepresentation_isIrreducible i
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
  · rintro ⟨e⟩
    let := IsIrreducible.nontrivial (ρ := D.blockRepresentation i) inferInstance
    refine ⟨e.toIntertwiningMap, ?_⟩
    intro he
    obtain ⟨x, hx⟩ := exists_ne (0 : D.block i)
    apply hx
    apply e.injective
    simpa using DFunLike.congr_fun he x

theorem coefficient_iff (sigma : Representation ℂ G W)
    [FiniteDimensional ℂ W] [IsIrreducible sigma] :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (rho.tprod sigma)) ↔
      ∃ i, Nonempty (Representation.Equiv (D.blockRepresentation i) sigma.dual) := by
  let := RepresentationTheory.dual_isIrreducible sigma
  exact (SelectionCriteria.allowed_equiv (InvariantTensorCurry.equiv rho sigma)).trans
    (irreducible_target_iff D sigma.dual)

theorem block_positive [FiniteDimensional ℂ V] (i : Fin D.numberOfBlocks) :
    0 < Module.finrank ℂ (D.block i) := by
  let : FiniteDimensional ℂ (D.block i) := FiniteDimensional.of_injective
    ((D.block i).subtype.restrictScalars ℂ) (D.block i).subtype_injective
  let := D.simple i
  let := IsSimpleModule.nontrivial ℂ[G] (D.block i)
  exact Module.finrank_pos

/-- Finiteness has a proved symbolic bound, even when every copy is kept. -/
theorem numberOfBlocks_le [FiniteDimensional ℂ V] :
    D.numberOfBlocks ≤ Module.finrank ℂ V := by
  calc
    _ = ∑ _i : Fin D.numberOfBlocks, 1 := by simp
    _ ≤ ∑ i, Module.finrank ℂ (D.block i) :=
      Finset.sum_le_sum (fun i _ => block_positive D i)
    _ = _ := D.sum_finrank

end
end Math.FiniteConstituentSupport
