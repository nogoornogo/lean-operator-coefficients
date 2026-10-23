import Math.RepresentationTheory.Constructions.TraceEndomorphismSplit
import Math.RepresentationTheory.Coefficients.InvariantCoefficientProduct
import Mathlib.Algebra.Algebra.Bilinear

/-! A genuine positive coupling of trace-free endomorphism branches.
Conjugation preserves trace of composition; off-diagonal rank-one maps
supply a normalized nonzero witness. No irreducibility is assumed. -/
namespace Math.TraceFreePairing
set_option autoImplicit false
noncomputable section
open Representation TraceEndomorphismSplit InvariantCoefficientProduct
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (r : Representation ℂ G V)

abbrev PairCarrier := TraceFree r ⊗[ℂ] TraceFree r
@[reducible] local instance : AddCommGroup (PairCarrier r) := inferInstance
abbrev pairAction : Representation ℂ G (PairCarrier r) := (traceFreeAction r).tprod (traceFreeAction r)

def coefficient : InvariantCoefficientTransport.Invariants (pairAction r) where
  toLinearMap := (LinearMap.trace ℂ V).comp ((LinearMap.mul' ℂ (Module.End ℂ V)).comp
    (TensorProduct.map (TraceFree r).subtype (TraceFree r).subtype))
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change LinearMap.trace ℂ V ((r g*x.val*r g⁻¹)*(r g*y.val*r g⁻¹))=
      LinearMap.trace ℂ V (x.val*y.val)
    have hp : (r g*x.val*r g⁻¹)*(r g*y.val*r g⁻¹)=r g*(x.val*y.val)*r g⁻¹ := by
      apply LinearMap.ext
      intro v
      change r g (x.val (r g⁻¹ (r g (y.val (r g⁻¹ v)))))=r g (x.val (y.val (r g⁻¹ v)))
      rw [Representation.inv_self_apply]
    rw [hp]
    exact (trace r).isIntertwining _ _ g (x.val*y.val)

omit [FiniteDimensional ℂ V] in
@[simp] theorem coefficient_pure (x y : TraceFree r) :
    coefficient r (x ⊗ₜ[ℂ] y)=LinearMap.trace ℂ V (x.val*y.val) := rfl

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ V) (i j : ι) (hij : i≠j)

def offDiagonal : TraceFree r :=
  ⟨(b.coord j).smulRight (b i),by
    change LinearMap.trace ℂ V ((b.coord j).smulRight (b i))=0
    rw [LinearMap.trace_smulRight]
    simp [Ne.symm hij]⟩

omit [Fintype ι] [DecidableEq ι] in
include b hij in
/-- Two opposite off-diagonal endomorphisms pair to one, in any basis. -/
theorem unit : HasUnit (pairAction r) := by
  let x := offDiagonal r b i j hij
  let y := offDiagonal r b j i hij.symm
  refine ⟨coefficient r,x ⊗ₜ[ℂ] y,?_⟩
  rw [coefficient_pure]
  have hp : x.val*y.val=(b.coord i).smulRight (b i) := by
    apply LinearMap.ext
    intro v
    change (b.coord j ((b.coord i v) • b j)) • b i=(b.coord i v) • b i
    simp
  rw [hp,LinearMap.trace_smulRight]
  simp

end
end Math.TraceFreePairing
