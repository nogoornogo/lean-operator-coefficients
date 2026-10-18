import Mathlib.RepresentationTheory.Intertwining

/-! Equivariant maps from an arbitrary direct sum are a product of residual Homs.
No finite-dimensionality or finite-index hypothesis is needed. -/
namespace Math.DirectSumResidualHom
set_option autoImplicit false
noncomputable section
open Representation
variable {k H I W : Type*} {V : I → Type*} [Field k] [Group H] [DecidableEq I]
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [AddCommGroup W] [Module k W]
  (a : ∀ i, Representation k H (V i)) (w : Representation k H W)

def assemble (f : ∀ i, IntertwiningMap (a i) w) :
    IntertwiningMap (Representation.directSum a) w where
  toLinearMap := DFinsupp.lsum k (fun i => (f i).toLinearMap)
  isIntertwining' h := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro v
    change DFinsupp.lsum k (fun i => (f i).toLinearMap)
      (DirectSum.lmap (fun i => a i h) (DirectSum.of V i v)) =
      w h (DFinsupp.lsum k (fun i => (f i).toLinearMap) (DFinsupp.single i v))
    rw [DirectSum.lmap_of]
    change DFinsupp.lsum k (fun i => (f i).toLinearMap) (DFinsupp.single i (a i h v)) = _
    simpa using IntertwiningMap.isIntertwining _ _ (f i) h v

@[simp] theorem assemble_single (f : ∀ i, IntertwiningMap (a i) w) (i : I) (v : V i) :
    assemble a w f (DFinsupp.single i v) = f i v := by
  exact DFinsupp.lsum_single k (fun i => (f i).toLinearMap) i v

def extract (f : IntertwiningMap (Representation.directSum a) w) (i : I) :
    IntertwiningMap (a i) w where
  toLinearMap := f.toLinearMap.comp (DFinsupp.lsingle i)
  isIntertwining' h := by
    ext v
    have hf := IntertwiningMap.isIntertwining _ _ f h (DFinsupp.single i v)
    change f (DirectSum.lmap (fun i => a i h) (DirectSum.of V i v)) = _ at hf
    rw [DirectSum.lmap_of] at hf
    exact hf

def equiv : (∀ i, IntertwiningMap (a i) w) ≃ₗ[k]
    IntertwiningMap (Representation.directSum a) w where
  toFun := assemble a w
  invFun := extract a w
  left_inv f := by funext i; ext v; change assemble a w f (DFinsupp.single i v) = _; simp
  right_inv f := by
    apply IntertwiningMap.ext
    apply DFinsupp.lhom_ext
    intro i v
    change assemble a w (extract a w f) (DFinsupp.single i v) = _
    rw [assemble_single]
    rfl
  map_add' f g := by
    apply IntertwiningMap.ext
    apply DFinsupp.lhom_ext
    intro i v
    change assemble a w (f + g) (DFinsupp.single i v) =
      assemble a w f (DFinsupp.single i v) + assemble a w g (DFinsupp.single i v)
    simp only [assemble_single]
    rfl
  map_smul' z f := by
    apply IntertwiningMap.ext
    apply DFinsupp.lhom_ext
    intro i v
    change assemble a w (z • f) (DFinsupp.single i v) =
      z • assemble a w f (DFinsupp.single i v)
    simp only [assemble_single]
    rfl

section Transport
variable {U : Type*} [AddCommGroup U] [Module k U]
  {u : Representation k H U}

/-- Transport a coefficient across a specified carrier equivalence. -/
def precomposeEquiv (e : Representation.Equiv (Representation.directSum a) u) :
    IntertwiningMap u w ≃ₗ[k] IntertwiningMap (Representation.directSum a) w where
  toFun f := f.comp e.toIntertwiningMap
  invFun f := f.comp e.symm.toIntertwiningMap
  left_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact congrArg f (e.apply_symm_apply v)
  right_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    exact congrArg f (e.symm_apply_apply v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Full residual coefficient classification by the independent summands. -/
def coefficientEquiv (e : Representation.Equiv (Representation.directSum a) u) :
    IntertwiningMap u w ≃ₗ[k] (∀ i, IntertwiningMap (a i) w) :=
  (precomposeEquiv a w e).trans (equiv a w).symm

@[simp] theorem coefficientEquiv_apply
    (e : Representation.Equiv (Representation.directSum a) u)
    (f : IntertwiningMap u w) (i : I) (v : V i) :
    coefficientEquiv a w e f i v = f (e (DFinsupp.single i v)) := rfl

end Transport

end
end Math.DirectSumResidualHom
