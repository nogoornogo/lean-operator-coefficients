import Math.RepresentationTheory.Decomposition.Schur
import Mathlib.LinearAlgebra.Pi
import Mathlib.Basic.Complex.Basic

namespace Math.FiniteBlockHom
set_option autoImplicit false
noncomputable section
open Representation
variable {G I J : Type*} [Group G] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]
  {A : I → Type*} {B : J → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]
  (a : ∀ i, Representation ℂ G (A i)) (b : ∀ j, Representation ℂ G (B j))

def action {T : Type*} {C : T → Type*} [∀ i, AddCommGroup (C i)] [∀ i, Module ℂ (C i)]
    (r : ∀ i, Representation ℂ G (C i)) : Representation ℂ G (∀ i, C i) where
  toFun g := LinearMap.pi fun i => (r i g).comp (LinearMap.proj i)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [map_mul]

omit [Fintype I] [DecidableEq I] in
@[simp] theorem action_apply (g : G) (x : ∀ i, A i) (i : I) : action a g x i = a i g (x i) := rfl

def project (i : I) : IntertwiningMap (action a) (a i) where
  toLinearMap := LinearMap.proj i
  isIntertwining' _ := rfl

def inject (i : I) : IntertwiningMap (a i) (action a) where
  toLinearMap := LinearMap.single ℂ A i
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    ext t
    by_cases h : t=i
    · subst t; simp [action]
    · simp [action,h]

def block (f : IntertwiningMap (action a) (action b)) (j : J) (i : I) :
    IntertwiningMap (a i) (b j) := (project b j).comp (f.comp (inject a i))

def assemble (m : ∀ j i, IntertwiningMap (a i) (b j)) :
    IntertwiningMap (action a) (action b) where
  toLinearMap := LinearMap.pi fun j => ∑ i, (m j i).toLinearMap.comp (LinearMap.proj i)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    ext j
    simp only [LinearMap.comp_apply,LinearMap.pi_apply,LinearMap.sum_apply,LinearMap.proj_apply,action_apply]
    change (∑ i, m j i (a i g (x i))) = b j g (∑ i, m j i (x i))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (m j i).isIntertwining _ _ g (x i)

omit [Fintype I] [Fintype J] [DecidableEq J] in
@[simp] theorem block_apply (f : IntertwiningMap (action a) (action b))
    (j : J) (i : I) (x : A i) : block a b f j i x = f (Pi.single i x) j := rfl

omit [DecidableEq I] [Fintype J] [DecidableEq J] in
@[simp] theorem assemble_apply (m : ∀ j i, IntertwiningMap (a i) (b j))
    (x : ∀ i, A i) (j : J) : assemble a b m x j = ∑ i, m j i (x i) := by
  simp [assemble,LinearMap.sum_apply]

def equiv : IntertwiningMap (action a) (action b) ≃ₗ[ℂ]
    (∀ j i, IntertwiningMap (a i) (b j)) where
  toFun := block a b
  invFun := assemble a b
  left_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hx : (∑ i, Pi.single i (x i)) = x := by ext t; simp
    ext j
    change assemble a b (block a b f) x j = f x j
    simp only [assemble_apply,block_apply]
    rw [← Finset.sum_apply,← map_sum,hx]
  right_inv m := by
    funext j i
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change block a b (assemble a b m) j i x = m j i x
    simp only [block_apply,assemble_apply]
    change (∑ t, m j t (Pi.single i x t)) = m j i x
    rw [Finset.sum_eq_single i]
    · simp
    · intro t _ ht
      have hz : Pi.single i x t = 0 := by simp [Pi.single,ht]
      rw [hz,map_zero]
    · simp
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
end
end Math.FiniteBlockHom
