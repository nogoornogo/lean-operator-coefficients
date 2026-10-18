import Math.RepresentationTheory.MultilinearInvariantHom
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Tactic

/-! The balanced fourfold tensor product and heterogeneous multilinear maps. -/
namespace Math.FourTensorMultilinear
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {V : Fin 4 → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

abbrev Tensor (V : Fin 4 → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] :=
  (V 0 ⊗[ℂ] V 1) ⊗[ℂ] (V 2 ⊗[ℂ] V 3)

def curried (f : MultilinearMap ℂ V W) : V 0 →ₗ[ℂ] V 1 →ₗ[ℂ] V 2 →ₗ[ℂ] V 3 →ₗ[ℂ] W :=
  f.curryRight.curryRight.curryRight.curryRight (fun i => nomatch i)

theorem curried_apply (f : MultilinearMap ℂ V W) (v : ∀ i, V i) :
    curried f (v 0) (v 1) (v 2) (v 3) = f v := by
  simp only [curried, MultilinearMap.curryRight_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

def lift (f : MultilinearMap ℂ V W) : Tensor V →ₗ[ℂ] W :=
  TensorProduct.lift (TensorProduct.lift
    ((LinearMap.compRight ℂ (TensorProduct.lift.equiv (RingHom.id ℂ) (V 2) (V 3) W).toLinearMap).comp
        (curried f)))

theorem lift_tprod (f : MultilinearMap ℂ V W) (v : ∀ i, V i) :
    lift f ((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)) = f v :=
  curried_apply f v

def evaluate (f : Tensor V →ₗ[ℂ] W) : MultilinearMap ℂ V W :=
  MultilinearMap.mk' (fun v => f ((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)))
    (by intro v i x y; fin_cases i <;>
      simp [Function.update, TensorProduct.add_tmul, TensorProduct.tmul_add])
    (by intro v i z x; fin_cases i <;>
      simp [Function.update, TensorProduct.smul_tmul, TensorProduct.tmul_smul])

def equiv : MultilinearMap ℂ V W ≃ₗ[ℂ] (Tensor V →ₗ[ℂ] W) where
  toFun := lift
  invFun := evaluate
  left_inv f := by ext v; exact lift_tprod f v
  right_inv f := by
    ext a b c d
    simp [lift, curried, MultilinearMap.curryRight_apply, evaluate, Fin.snoc]
    rfl
  map_add' f g := by
    ext a b c d
    simp [lift, curried, MultilinearMap.curryRight_apply]
  map_smul' z f := by
    ext a b c d
    simp [lift, curried, MultilinearMap.curryRight_apply]

section Invariant
variable {G : Type*} [Group G] (r : ∀ i, Representation ℂ G (V i))

def representation := ((r 0).tprod (r 1)).tprod ((r 2).tprod (r 3))

/-- Invariance with a fifth, linear input survives fourfold tensor descent. -/
theorem lift_diagonal_iff {B : Type*} [AddCommGroup B] [Module ℂ B]
    (t : Representation ℂ G B)
    (f : MultilinearMap ℂ V (B →ₗ[ℂ] ℂ)) :
    (∀ g v b, f (fun i => r i g (v i)) (t g b) = f v b) ↔
    (∀ g x b, lift f (representation r g x) (t g b) = lift f x b) := by
  constructor
  · intro h g x w
    have hl : (LinearMap.applyₗ (R := ℂ) (M₂ := ℂ) (t g w)).comp
        ((lift f).comp (representation r g)) =
        (LinearMap.applyₗ (R := ℂ) (M₂ := ℂ) w).comp (lift f) := by
      ext a b c d
      let v : ∀ i, V i := Fin.cons a (Fin.cons b (Fin.cons c
        (Fin.cons d (fun i => nomatch i))))
      change lift f (((r 0 g a) ⊗ₜ[ℂ] (r 1 g b)) ⊗ₜ[ℂ]
        ((r 2 g c) ⊗ₜ[ℂ] (r 3 g d))) (t g w) =
          lift f ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) w
      change lift f (((r 0 g (v 0)) ⊗ₜ[ℂ] (r 1 g (v 1))) ⊗ₜ[ℂ]
        ((r 2 g (v 2)) ⊗ₜ[ℂ] (r 3 g (v 3)))) (t g w) =
          lift f ((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)) w
      rw [lift_tprod f (fun i => r i g (v i)), lift_tprod]
      exact h g v w
    exact LinearMap.congr_fun hl x
  · intro h g v b
    have hv := h g ((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)) b
    change lift f (((r 0 g (v 0)) ⊗ₜ[ℂ] (r 1 g (v 1))) ⊗ₜ[ℂ]
      ((r 2 g (v 2)) ⊗ₜ[ℂ] (r 3 g (v 3)))) (t g b) = _ at hv
    rw [lift_tprod f (fun i => r i g (v i)), lift_tprod] at hv
    exact hv

/-- A fifth linear slot can be tensorized without assuming that its action is trivial. -/
def diagonalInvariantLift {B : Type*} [AddCommGroup B] [Module ℂ B]
    (t : Representation ℂ G B)
    (f : MultilinearMap ℂ V (B →ₗ[ℂ] ℂ))
    (hf : ∀ g v b, f (fun i => r i g (v i)) (t g b) = f v b) :
    Representation.IntertwiningMap ((representation r).tprod t)
      (Representation.trivial ℂ G ℂ) where
  toLinearMap := TensorProduct.lift (lift f)
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro x
    apply LinearMap.ext; intro b
    exact (lift_diagonal_iff r t f).mp hf g x b

theorem diagonalInvariantLift_pure {B : Type*} [AddCommGroup B] [Module ℂ B]
    (t : Representation ℂ G B)
    (f : MultilinearMap ℂ V (B →ₗ[ℂ] ℂ))
    (hf : ∀ g v b, f (fun i => r i g (v i)) (t g b) = f v b)
    (v : ∀ i, V i) (b : B) :
    diagonalInvariantLift r t f hf
      (((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3)) ⊗ₜ[ℂ] b) = f v b :=
  LinearMap.congr_fun (lift_tprod f v) b

def invariantLift (f : MultilinearInvariantHom.invariantMaps (W := W) r) :
    Representation.IntertwiningMap (representation r) (Representation.trivial ℂ G W) where
  toLinearMap := lift f.val
  isIntertwining' g := by
    ext a b c d
    simp [representation, lift, curried, MultilinearMap.curryRight_apply]
    convert f.property g
      (Fin.cons a (Fin.cons b (Fin.cons c (Fin.cons d (fun i => nomatch i))))) using 1 <;>
      congr 1 <;> funext i <;> fin_cases i <;> rfl

def invariantEvaluate (f : Representation.IntertwiningMap (representation r)
    (Representation.trivial ℂ G W)) : MultilinearInvariantHom.invariantMaps (W := W) r :=
  ⟨evaluate f.toLinearMap, by
    intro g v
    exact Representation.IntertwiningMap.isIntertwining _ _ f g
      ((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] (v 2 ⊗ₜ[ℂ] v 3))⟩

def invariantEquiv : MultilinearInvariantHom.invariantMaps (W := W) r ≃ₗ[ℂ]
    Representation.IntertwiningMap (representation r) (Representation.trivial ℂ G W) where
  toFun := invariantLift r
  invFun := invariantEvaluate r
  left_inv f := by apply Subtype.ext; exact equiv.left_inv f.val
  right_inv f := by apply Representation.IntertwiningMap.ext; exact equiv.right_inv f.toLinearMap
  map_add' f g := by apply Representation.IntertwiningMap.ext; exact equiv.map_add f.val g.val
  map_smul' z f := by apply Representation.IntertwiningMap.ext; exact equiv.map_smul z f.val

end Invariant

end
end Math.FourTensorMultilinear
