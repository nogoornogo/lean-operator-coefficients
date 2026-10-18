import Math.RepresentationTheory.MixedPatternAssembly
import Math.RepresentationTheory.MultilinearInvariantHom

/-! Actual ordered heterogeneous tensors and typed mixed multilinear maps. -/
namespace Math.TypedMixedTensorHom
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {I J G : Type*} [Fintype I] [Fintype J] [Group G]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]

abbrev Domain := (⨂[ℂ] i, V i) ⊗[ℂ] (⨂[ℂ] j, W j)
abbrev Ordered := MultilinearMap ℂ V (MultilinearMap ℂ W ℂ)

omit [Fintype I] [Fintype J] in
theorem pure_ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : Domain (V := V) (W := W) →ₗ[ℂ] N}
    (he : ∀ v w, f (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w) =
      g (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w)) : f = g := by
  apply TensorProduct.ext'
  intro x y
  induction x using PiTensorProduct.induction_on with
  | smul_tprod z v =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod u w =>
      simp only [TensorProduct.smul_tmul_smul, map_smul]
      rw [he]
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']

def orderedEquiv : (Domain (V := V) (W := W) →ₗ[ℂ] ℂ) ≃ₗ[ℂ]
    Ordered (V := V) (W := W) :=
  (TensorProduct.lift.equiv (RingHom.id ℂ) (⨂[ℂ] i, V i) (⨂[ℂ] j, W j) ℂ).symm.trans
    ((LinearEquiv.arrowCongr (LinearEquiv.refl ℂ (⨂[ℂ] i, V i)) PiTensorProduct.lift.symm).trans
      PiTensorProduct.lift.symm)

omit [Fintype I] [Fintype J] in
@[simp] theorem orderedEquiv_apply (f : Domain (V := V) (W := W) →ₗ[ℂ] ℂ)
    (v : ∀ i, V i) (w : ∀ j, W j) :
    orderedEquiv f v w = f (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w) := rfl

omit [Fintype I] [Fintype J] in
@[simp] theorem lift_apply (k : Ordered (V := V) (W := W))
    (v : ∀ i, V i) (w : ∀ j, W j) :
    orderedEquiv.symm k (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w) = k v w := by
  simpa only [orderedEquiv_apply] using congrArg
    (fun f : Ordered (V := V) (W := W) => f v w) (orderedEquiv.apply_symm_apply k)

omit [Fintype I] [Fintype J] in
theorem ext {f g : Domain (V := V) (W := W) →ₗ[ℂ] ℂ}
    (he : ∀ v w, f (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w) =
      g (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w)) : f = g := by
  apply orderedEquiv.injective
  ext v w
  exact he v w

variable (a : ∀ i, Representation ℂ G (V i)) (b : ∀ j, Representation ℂ G (W j))

def invariantOrdered : Submodule ℂ (Ordered (V := V) (W := W)) where
  carrier := {k | ∀ h v w, k (fun i => a i h (v i)) (fun j => b j h (w j)) = k v w}
  zero_mem' := by intro h v w; rfl
  add_mem' := by
    intro k l hk hl h v w
    change k _ _ + l _ _ = k _ _ + l _ _
    rw [hk, hl]
  smul_mem' := by
    intro z k hk h v w
    change z • k _ _ = z • k _ _
    rw [hk]

def assemble (k : invariantOrdered a b) :
    IntertwiningMap ((MultilinearInvariantHom.tensorRepresentation a).tprod
      (MultilinearInvariantHom.tensorRepresentation b)) (trivial ℂ G ℂ) where
  toLinearMap := orderedEquiv.symm k.val
  isIntertwining' h := by
    apply ext
    intro v w
    change orderedEquiv.symm k.val
      (((MultilinearInvariantHom.tensorRepresentation a).tprod
        (MultilinearInvariantHom.tensorRepresentation b)) h
          (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w)) =
      orderedEquiv.symm k.val (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w)
    rw [Representation.tprod_apply, TensorProduct.map_tmul,
      MultilinearInvariantHom.tensorRepresentation_tprod,
      MultilinearInvariantHom.tensorRepresentation_tprod, lift_apply, lift_apply]
    exact k.property h v w

def equiv : IntertwiningMap ((MultilinearInvariantHom.tensorRepresentation a).tprod
    (MultilinearInvariantHom.tensorRepresentation b)) (trivial ℂ G ℂ) ≃ₗ[ℂ] invariantOrdered a b where
  toFun f := ⟨orderedEquiv f.toLinearMap, by
    intro h v w
    have he := IntertwiningMap.isIntertwining _ _ f h
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w)
    simpa only [orderedEquiv_apply, Representation.tprod_apply, TensorProduct.map_tmul,
      MultilinearInvariantHom.tensorRepresentation_tprod, Representation.trivial_apply,
      LinearMap.id_apply, IntertwiningMap.toLinearMap_apply] using he⟩
  invFun := assemble a b
  left_inv f := by apply IntertwiningMap.ext; exact orderedEquiv.symm_apply_apply f.toLinearMap
  right_inv k := by apply Subtype.ext; exact orderedEquiv.apply_symm_apply k.val
  map_add' f g := by apply Subtype.ext; exact orderedEquiv.map_add _ _
  map_smul' z f := by apply Subtype.ext; exact orderedEquiv.map_smul z _

end
end Math.TypedMixedTensorHom
