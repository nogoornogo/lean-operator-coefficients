import Math.RepresentationTheory.TraceFreeCoefficientExclusion
import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation
import Math.RepresentationTheory.Decomposition.TensorProductSums

/-! Actual equivalence of trace-free endomorphisms on a representation
and its dual. Whole endomorphism actions are compared by tensor/bidual
maps; proved finite summand cancellation removes the scalar part.
No irreducibility or adjoint self-duality premise is needed. -/
namespace Math.TraceFreeDualEnd
set_option autoImplicit false
noncomputable section
open Representation TraceEndomorphismSplit ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (r : Representation ℂ G V)
@[reducible] local instance : AddCommGroup (TraceFree r) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (TraceFree r.dual) := Module.addCommMonoidToAddCommGroup ℂ

def whole : Representation.Equiv (action r) (action r.dual) :=
  (TraceFreeCoefficientExclusion.tensorEnd r).symm.trans
    ((Representation.TensorProduct.comm r r.dual).trans
      ((tensorEquiv (.refl r.dual) (bidualEquiv r)).trans
        (TraceFreeCoefficientExclusion.tensorEnd r.dual)))

variable (hd : Module.finrank ℂ V≠0)

def scalarComparison : Representation.Equiv
    ((traceFreeAction r).prod (trivial ℂ G ℂ))
    ((traceFreeAction r.dual).prod (trivial ℂ G ℂ)) :=
  (TensorProductSums.prodComm (traceFreeAction r) (trivial ℂ G ℂ)).trans
    ((TraceEndomorphismSplit.equivalence r hd).trans
      ((whole r).trans ((TraceEndomorphismSplit.equivalence r.dual (by
        rw [Subspace.dual_finrank_eq]; exact hd)).symm.trans
          (TensorProductSums.prodComm (trivial ℂ G ℂ) (traceFreeAction r.dual)))))

def equivalence : Representation.Equiv (traceFreeAction r) (traceFreeAction r.dual) :=
  Classical.choice (FiniteSummandCancellation.nonempty_equiv
    (A := TraceFree r) (B := TraceFree r.dual) (C := ℂ)
    (traceFreeAction r) (traceFreeAction r.dual) (trivial ℂ G ℂ) (scalarComparison r hd))

end
end Math.TraceFreeDualEnd
