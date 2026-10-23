import Math.RepresentationTheory.Tensors.ExternalInvariantTensor

namespace Math.ExternalUnitEquivalence
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct
variable {G H V : Type*} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]

def equiv (r : Representation ℂ G V) :
    Representation.Equiv (external r (trivial ℂ H ℂ)) (r.comp (MonoidHom.fst G H)) where
  toLinearEquiv := _root_.TensorProduct.rid ℂ V
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro v z
    simp [external,Representation.tprod_apply,TensorProduct.rid_tmul]
end
end Math.ExternalUnitEquivalence
