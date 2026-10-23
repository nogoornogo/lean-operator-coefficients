import Math.RepresentationTheory.Relations.LocalRelationHom
import Math.RepresentationTheory.Relations.LocalCoinvariantTensor

/-! Explicit residual carrier `(L_G ⊗ M) / image(exchange relations)`. -/
namespace Math.LocalRelationTensorHom
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {k G H L M : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup L] [Module k L] [AddCommGroup M] [Module k M]
  (a : Representation k G L) (b : Representation k H M)
  (R : Submodule k (L ⊗[k] M))
  (stable : ∀ h, R ≤ R.comap (LocalCoinvariantTensor.residual (L := L) b h))

abbrev base := (trivial k H (L ⧸ LocalCoinvariantHom.relations a)).tprod b
abbrev relations := (LocalRelationHom.image (LocalCoinvariantTensor.action (M := M) a) R).map
  (LocalCoinvariantTensor.residualEquiv a b).symm.toLinearMap

include stable in
theorem relations_stable : ∀ h, relations a b R ≤ (relations a b R).comap (base a b h) :=
  RelationQuotient.map_stable _ _
    (LocalRelationHom.image_stable _ _ (LocalCoinvariantTensor.commutes a b) R stable)
    (LocalCoinvariantTensor.residualEquiv a b).symm

abbrev residual := (base a b).quotient (relations a b R) (relations_stable a b R stable)

abbrev Carrier := ((L ⧸ LocalCoinvariantHom.relations a) ⊗[k] M) ⧸ relations a b R

def equiv : LocalRelationHom.Input (LocalCoinvariantTensor.action (M := M) a)
    (LocalCoinvariantTensor.residual (L := L) b) (trivial k H k) R ≃ₗ[k]
    IntertwiningMap (residual a b R stable) (trivial k H k) :=
  (LocalRelationHom.constrainedEquiv _ _ (trivial k H k) (LocalCoinvariantTensor.commutes a b) R).trans
    ((RelationQuotient.alongEquiv _ (trivial k H k) _
      (LocalCoinvariantTensor.residualEquiv a b).symm).trans
      (RelationQuotient.equiv (base a b) (trivial k H k) (relations a b R)
        (relations_stable a b R stable)))

end
end Math.LocalRelationTensorHom
