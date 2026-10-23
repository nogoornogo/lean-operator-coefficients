import Math.RepresentationTheory.Tensors.TraceFreePairing

/-! A normalized trilinear trace coefficient on actual trace-free branches.
The invariant identity is conjugation of a product; the witness is a cycle
of off-diagonal rank-one maps, with no irreducibility assumption. -/
namespace Math.TraceFreeTrilinear
set_option autoImplicit false
noncomputable section
open Representation TraceEndomorphismSplit InvariantCoefficientProduct
open scoped TensorProduct
@[reducible] local instance (A B : Type*) [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] : AddCommGroup (A ⊗[ℂ] B) := inferInstance
variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (r : Representation ℂ G V)
abbrev Carrier := (TraceFree r ⊗[ℂ] TraceFree r) ⊗[ℂ] TraceFree r
@[reducible] local instance : AddCommGroup (TraceFree r ⊗[ℂ] TraceFree r) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance : AddCommGroup (Carrier r) := Module.addCommMonoidToAddCommGroup ℂ
abbrev action : Representation ℂ G (Carrier r) :=
  ((traceFreeAction r).tprod (traceFreeAction r)).tprod (traceFreeAction r)

def multiplyTwo : TraceFree r ⊗[ℂ] TraceFree r →ₗ[ℂ] Module.End ℂ V :=
  (LinearMap.mul' ℂ (Module.End ℂ V)).comp
    (TensorProduct.map (TraceFree r).subtype (TraceFree r).subtype)

def coefficient : InvariantCoefficientTransport.Invariants (action r) where
  toLinearMap := (LinearMap.trace ℂ V).comp
    ((LinearMap.mul' ℂ (Module.End ℂ V)).comp
      (TensorProduct.map (multiplyTwo r) (TraceFree r).subtype))
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change LinearMap.trace ℂ V
      ((r g*x.val*r g⁻¹)*(r g*y.val*r g⁻¹)*(r g*z.val*r g⁻¹))=
      LinearMap.trace ℂ V (x.val*y.val*z.val)
    have hp : (r g*x.val*r g⁻¹)*(r g*y.val*r g⁻¹)*(r g*z.val*r g⁻¹)=
        r g*(x.val*y.val*z.val)*r g⁻¹ := by
      apply LinearMap.ext
      intro v
      change r g (x.val (r g⁻¹ (r g (y.val (r g⁻¹ (r g (z.val (r g⁻¹ v))))))))=
        r g (x.val (y.val (z.val (r g⁻¹ v))))
      rw [Representation.inv_self_apply,Representation.inv_self_apply]
    rw [hp]
    exact (trace r).isIntertwining _ _ g (x.val*y.val*z.val)

omit [FiniteDimensional ℂ V] in
@[simp] theorem coefficient_pure (x y z : TraceFree r) :
    coefficient r ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)=LinearMap.trace ℂ V (x.val*y.val*z.val) := rfl

theorem unit (b : Module.Basis (Fin 3) ℂ V) : HasUnit (action r) := by
  let x := TraceFreePairing.offDiagonal r b 0 1 (by decide)
  let y := TraceFreePairing.offDiagonal r b 1 2 (by decide)
  let z := TraceFreePairing.offDiagonal r b 2 0 (by decide)
  refine ⟨coefficient r,(x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z,?_⟩
  rw [coefficient_pure]
  have hp : x.val*y.val*z.val=(b.coord 0).smulRight (b 0) := by
    apply LinearMap.ext
    intro v
    change (b.coord 1 ((b.coord 2 ((b.coord 0 v) • b 2)) • b 1)) • b 0=(b.coord 0 v) • b 0
    simp
  rw [hp,LinearMap.trace_smulRight]
  simp

end
end Math.TraceFreeTrilinear
