import Math.RepresentationTheory.FourTensorMultilinear

/-! Two-sided tensor descent for four heterogeneous multilinear slots and one
linear slot, retaining the action on the last slot. -/
namespace Math.FourTensorLinearSlot
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G : Type*} [Group G] {V : Fin 4 → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {B : Type*} [AddCommGroup B] [Module ℂ B]
  (r : ∀ i, Representation ℂ G (V i)) (t : Representation ℂ G B)

def maps : Submodule ℂ (MultilinearMap ℂ V (B →ₗ[ℂ] ℂ)) where
  carrier := {f | ∀ g v b, f (fun i => r i g (v i)) (t g b) = f v b}
  zero_mem' := by intro g v b; rfl
  add_mem' := by
    intro f h hf hh g v b
    change f _ _ + h _ _ = f _ _ + h _ _
    rw [hf, hh]
  smul_mem' := by
    intro z f hf g v b
    change z * f _ _ = z * f _ _
    rw [hf]

abbrev invariants := IntertwiningMap ((FourTensorMultilinear.representation r).tprod t)
  (Representation.trivial ℂ G ℂ)

def lift (f : maps r t) : invariants r t :=
  FourTensorMultilinear.diagonalInvariantLift r t f.val f.property

def evaluate (f : invariants r t) : maps r t :=
  ⟨FourTensorMultilinear.evaluate (TensorProduct.curry f.toLinearMap), by
    intro g v b
    exact IntertwiningMap.isIntertwining _ _ f g
      (((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)) ⊗ₜ[ℂ] b)⟩

theorem lift_pure (f : maps r t) (v : ∀ i, V i) (b : B) :
    lift r t f (((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)) ⊗ₜ[ℂ] b) = f.val v b :=
  FourTensorMultilinear.diagonalInvariantLift_pure r t f.val f.property v b

theorem lift_cons (f : maps r t) (a : V 0) (b : V 1) (c : V 2) (d : V 3) (w : B) :
    lift r t f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w) =
      f.val (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (fun i => nomatch i))))) w := by
  exact lift_pure r t f
    (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (fun i => nomatch i))))) w

def equiv : maps r t ≃ₗ[ℂ] invariants r t where
  toFun := lift r t
  invFun := evaluate r t
  left_inv f := by
    apply Subtype.ext
    ext v b
    exact lift_pure r t f v b
  right_inv f := by
    ext a b c d w
    change lift r t (evaluate r t f) (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w) =
      f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w)
    rw [lift_cons]
    rfl
  map_add' f h := by
    ext a b c d w
    change lift r t (f + h) (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w) =
      lift r t f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w) +
      lift r t h (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w)
    rw [lift_cons, lift_cons, lift_cons]
    rfl
  map_smul' z f := by
    ext a b c d w
    change lift r t (z • f) (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w) =
      z * lift r t f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] w)
    rw [lift_cons, lift_cons]
    rfl

end
end Math.FourTensorLinearSlot
