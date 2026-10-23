import Math.RepresentationTheory.Color.SU3.SU3DefiningExterior
import Math.RepresentationTheory.Constructions.TraceEndomorphismSplit

/-! The actual SU3 defining/dual color pair, with its scalar and trace-free
parts kept equivariantly. No adjoint irreducibility or tensor-product
positivity rule is supplied as a premise. -/
namespace Math.SU3ColorPair
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior
open scoped TensorProduct

@[reducible] local instance : AddCommGroup (Vector ⊗[ℂ] Module.Dual ℂ Vector) := inferInstance

abbrev colorPair := rho.tprod rho.dual
abbrev Adjoint := TraceEndomorphismSplit.TraceFree rho
abbrev adjoint := TraceEndomorphismSplit.traceFreeAction rho

theorem dimension_nonzero : Module.finrank ℂ Vector≠0 := by rw [dimension]; omega

def tensorEndEquiv : Representation.Equiv colorPair (TraceEndomorphismSplit.action rho) :=
  (Representation.TensorProduct.comm rho rho.dual).trans
    (Representation.Equiv.dualTensorHom rho rho)

/-- Complete color pair splitting. Irreducibility of the trace-free branch
and its further products remain separate obligations. -/
def equivalence : Representation.Equiv colorPair ((trivial ℂ Group ℂ).prod adjoint) :=
  tensorEndEquiv.trans (TraceEndomorphismSplit.equivalence rho dimension_nonzero).symm

def coefficient : InvariantCoefficientTransport.Invariants colorPair :=
  (IntertwiningMap.fst ℂ (trivial ℂ Group ℂ) adjoint).comp equivalence.toIntertwiningMap

theorem coefficient_nonzero : coefficient≠0 := by
  intro hz
  have he := DFunLike.congr_fun hz (equivalence.symm (1,0))
  change (equivalence (equivalence.symm (1,0))).1=0 at he
  rw [Representation.Equiv.apply_symm_apply] at he
  exact one_ne_zero he

/-- The entire scalar coefficient space is a line, via actual curry,
biduality and the proved irreducibility of the defining representation. -/
def coefficientEquiv : InvariantCoefficientTransport.Invariants colorPair ≃ₗ[ℂ] ℂ :=
  (InvariantTensorCurry.equiv rho rho.dual).trans
    ((InvariantTensorCurry.postcompose rho rho.dual.dual
      (SplitRepresentationProjection.bidualEquiv rho).symm).trans
        (IrreducibleHomScalar.equiv rho rho (.refl rho)).symm)

theorem fixed_adjoint_zero (x : Adjoint) (hx : ∀ g, adjoint g x=x) : x=0 :=
  TraceEndomorphismSplit.fixed_traceFree_zero rho dimension_nonzero x hx

end
end Math.SU3ColorPair
