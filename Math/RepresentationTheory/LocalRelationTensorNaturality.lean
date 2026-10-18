import Math.RepresentationTheory.LocalRelationTensorHom
import Math.RepresentationTheory.LocalRelationNaturality

/-! Carrier-level separation is independent of any coefficient completeness map. -/
namespace Math.LocalRelationTensorNaturality
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {k G H L M : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup L] [Module k L] [AddCommGroup M] [Module k M]
  (a : Representation k G L) (b : Representation k H M)
  (R : Submodule k (L ⊗[k] M))
  (hr : ∀ h, R ≤ R.comap (LocalCoinvariantTensor.residual (L := L) b h))

def carrierEquiv : Representation.Equiv
    (LocalRelationHom.residual (LocalCoinvariantTensor.action (M := M) a)
      (LocalCoinvariantTensor.residual (L := L) b) (LocalCoinvariantTensor.commutes a b) R hr)
    (LocalRelationTensorHom.residual a b R hr) :=
  RelationQuotientNaturality.quotientEquiv
    (LocalCoinvariantHom.quotient (LocalCoinvariantTensor.action (M := M) a)
      (LocalCoinvariantTensor.residual (L := L) b) (LocalCoinvariantTensor.commutes a b))
    (LocalRelationTensorHom.base a b)
    (LocalRelationHom.image (LocalCoinvariantTensor.action (M := M) a) R)
    (LocalRelationTensorHom.relations a b R)
    (LocalRelationHom.image_stable _ _ (LocalCoinvariantTensor.commutes a b) R hr)
    (LocalRelationTensorHom.relations_stable a b R hr)
    (LocalCoinvariantTensor.residualEquiv a b).symm rfl

theorem extraction (q : LocalRelationHom.Input (LocalCoinvariantTensor.action (M := M) a)
    (LocalCoinvariantTensor.residual (L := L) b) (trivial k H k) R) :
    LocalRelationTensorHom.equiv a b R hr q =
    (LocalRelationHom.equiv _ _ (trivial k H k) (LocalCoinvariantTensor.commutes a b) R hr q).comp
      (carrierEquiv a b R hr).symm.toIntertwiningMap := by
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  obtain ⟨u,rfl⟩ := (LocalRelationTensorHom.relations a b R).mkQ_surjective u
  rfl

theorem extraction_generator (q : LocalRelationHom.Input
    (LocalCoinvariantTensor.action (M := M) a)
    (LocalCoinvariantTensor.residual (L := L) b) (trivial k H k) R)
    (l : L) (m : M) :
    LocalRelationTensorHom.equiv a b R hr q
      ((LocalRelationTensorHom.relations a b R).mkQ
        ((LocalCoinvariantHom.relations a).mkQ l ⊗ₜ[k] m)) = q.val.val (l ⊗ₜ[k] m) := by
  change LocalCoinvariantHom.equiv _ _ _ (LocalCoinvariantTensor.commutes a b) q.val
    (LocalCoinvariantTensor.equiv a ((LocalCoinvariantHom.relations a).mkQ l ⊗ₜ[k] m)) = _
  rw [LocalCoinvariantTensor.equiv_tmul_mk]
  rfl
end
end Math.LocalRelationTensorNaturality
