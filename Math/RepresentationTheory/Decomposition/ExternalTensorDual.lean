import Math.RepresentationTheory.ExternalInvariantTensor
import Math.RepresentationTheory.Decomposition.ExternalTensorProduct

/-! Equivariant finite-dimensional tensor duality for independent actions. -/

namespace Math.ExternalTensorDual
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct

variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (a : Representation ℂ G V) (b : Representation ℂ H W)

def equiv : Representation.Equiv (external a.dual b.dual) (external a b).dual where
  toLinearEquiv := TensorProduct.dualDistribEquiv ℂ V W
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro phi psi
    apply TensorProduct.ext'
    intro x y
    simp [external, Representation.tprod_apply, Representation.dual_apply,
      Module.Dual.transpose_apply]

/-- The right-handed model uses the original gauge representation and the
dual multiplicity, whereas the left-handed gauge representation is dual. -/
def rightModelEquiv :
    Representation.Equiv (external a.dual b).dual (external a b.dual) :=
  (equiv a.dual b).symm.trans
    (externalEquiv (bidualEquiv a).symm (Representation.Equiv.refl b.dual))

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem external_eq (a : Representation ℂ G V) (b : Representation ℂ H W) :
    external a b = ExternalTensorProduct.externalTprod a b := rfl

end
end Math.ExternalTensorDual
