import Math.RepresentationTheory.TraceEndomorphismSplit
import Math.RepresentationTheory.InvariantTensorCurry
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.LinearAlgebra.SelectionCriteria

/-! Invariant scalar coefficients vanish on trace-free endomorphisms of an
irreducible finite-dimensional complex representation. Schur's scalar line
is used on the entire endomorphism space; trace-free irreducibility and a
trace-form duality premise are not needed. -/
namespace Math.TraceFreeCoefficientExclusion
set_option autoImplicit false
noncomputable section
open Representation TraceEndomorphismSplit InvariantCoefficientTransport
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (r : Representation ℂ G V)

def tensorEnd : Representation.Equiv (r.tprod r.dual) (action r) :=
  (Representation.TensorProduct.comm r r.dual).trans (Representation.Equiv.dualTensorHom r r)

def coefficientLine [IsIrreducible r] : Invariants (action r) ≃ₗ[ℂ] ℂ :=
  (alongEquiv (tensorEnd r)).symm.trans
    ((InvariantTensorCurry.equiv r r.dual).trans
      ((InvariantTensorCurry.postcompose r r.dual.dual
        (SplitRepresentationProjection.bidualEquiv r).symm).trans
          (IrreducibleHomScalar.equiv r r (.refl r)).symm))

variable (hd : Module.finrank ℂ V≠0)

theorem freePart_scalar (z : ℂ) : freePart r hd (scalar r z)=0 := by
  apply Subtype.ext
  change scalar r z-scalar r (project r (scalar r z))=0
  rw [project_scalar r hd,sub_self]

theorem freePart_traceFree (x : TraceFree r) : freePart r hd x.val=x := by
  apply Subtype.ext
  change x.val-scalar r (project r x.val)=x.val
  rw [project_traceFree,map_zero,sub_zero]

include hd in
theorem coefficient_zero [IsIrreducible r] (f : Invariants (traceFreeAction r)) : f=0 := by
  let F : Invariants (action r) := f.comp (freePart r hd)
  have hp : project r≠0 := by
    intro h
    have he := DFunLike.congr_fun h (scalar r 1)
    change project r (scalar r 1)=0 at he
    rw [project_scalar r hd] at he
    exact one_ne_zero he
  have hn : coefficientLine r (project r)≠0 := by
    intro h
    apply hp
    apply (coefficientLine r).injective
    simpa only [map_zero] using h
  let a : ℂ := coefficientLine r F / coefficientLine r (project r)
  have hF : F=a • project r := by
    apply (coefficientLine r).injective
    rw [map_smul,smul_eq_mul]
    exact (div_mul_cancel₀ _ hn).symm
  have he := congrArg (fun k : Invariants (action r) => k (scalar r 1)) hF
  change f (freePart r hd (scalar r 1))=a * project r (scalar r 1) at he
  rw [freePart_scalar,map_zero,project_scalar r hd,mul_one] at he
  have ha : a=0 := he.symm
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hF x.val
  change f (freePart r hd x.val)=a * project r x.val at hx
  rw [freePart_traceFree,ha,zero_mul] at hx
  exact hx

include hd in
theorem forbidden [IsIrreducible r] : SelectionCriteria.Forbidden (Invariants (traceFreeAction r)) :=
  fun f => coefficient_zero r hd f

end
end Math.TraceFreeCoefficientExclusion
