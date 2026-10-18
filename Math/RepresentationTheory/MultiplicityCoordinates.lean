import Math.RepresentationTheory.IsotypicResidual

/-! Chosen multiplicity coordinates retain the entire residual action, including
mixing between copies. No finiteness hypothesis on the multiplicity is needed. -/
namespace Math.MultiplicityCoordinates
set_option autoImplicit false
noncomputable section
open Representation
universe u
variable {M : Type u} {R H N P : Type*} [Ring R] [Group H]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  (rho : Representation R H M) (e : M ≃ₗ[R] N)

/-- The residual action in chosen coordinates; copies may mix. -/
def action : Representation R H N where
  toFun h := e.toLinearMap.comp ((rho h).comp e.symm.toLinearMap)
  map_one' := by ext u; simp
  map_mul' h j := by ext u; simp [map_mul, Module.End.mul_apply]

@[simp] theorem action_apply (h : H) (u : N) :
    action rho e h u = e (rho h (e.symm u)) := rfl

def equiv : Representation.Equiv rho (action rho e) where
  toLinearEquiv := e
  isIntertwining' h := by ext u; simp

/-- Changing coordinates preserves the full residual representation. -/
def conversion (f : M ≃ₗ[R] P) :
    Representation.Equiv (action rho e) (action rho f) :=
  (equiv rho e).symm.trans (equiv rho f)

@[simp] theorem conversion_apply (f : M ≃ₗ[R] P) (u : N) :
    conversion rho e f u = f (e.symm u) := rfl

@[simp] theorem conversion_inverse (f : M ≃ₗ[R] P) (u : N) :
    conversion rho f e (conversion rho e f u) = u := by simp

section Isotypic
variable [IsSemisimpleModule R M]

omit [IsSemisimpleModule R M] in
/-- Every intrinsic block has actual simple-copy coordinates, not merely a label. -/
theorem exists_block_coordinates (c : IsotypicResidual.Index (R := R) (M := M)) :
    ∃ (I : Type u) (_ : Nonempty I) (V : Submodule R c.1),
      IsSimpleModule R V ∧ Nonempty (c.1 ≃ₗ[R] I →₀ V) :=
  (IsIsotypic.isotypicComponents c.2).linearEquiv_finsupp

end Isotypic
end

section Coefficients
noncomputable section
open Representation
variable {k H M N W : Type*} [Field k] [Group H]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup W] [Module k W]
  (rho : Representation k H M) (e : M ≃ₗ[k] N) (w : Representation k H W)

/-- Coefficients retain all residual constraints in multiplicity coordinates. -/
def coefficientEquiv : IntertwiningMap rho w ≃ₗ[k]
    IntertwiningMap (action rho e) w where
  toFun f := f.comp (equiv rho e).symm.toIntertwiningMap
  invFun f := f.comp (equiv rho e).toIntertwiningMap
  left_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    exact congrArg f (e.symm_apply_apply u)
  right_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro u
    exact congrArg f (e.apply_symm_apply u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coefficientEquiv_apply (f : IntertwiningMap rho w) (u : N) :
    coefficientEquiv rho e w f u = f (e.symm u) := rfl

@[simp] theorem coefficientEquiv_inverse (f : IntertwiningMap (action rho e) w) (u : M) :
    (coefficientEquiv rho e w).symm f u = f (e u) := rfl

end
end Coefficients
end Math.MultiplicityCoordinates
