import Math.RepresentationTheory.Decomposition.FiniteBlockHom
import Math.RepresentationTheory.Tensors.ExternalInvariantTensor
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! Finite direct sums commute with external tensor products. This is a
complete representation equivalence; no dimension or support is assumed. -/
namespace Math.FiniteExternalProducts
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor
open scoped TensorProduct
variable {G H I J : Type*} [Group G] [Group H] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J]
  {A : I → Type*} {B : J → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]

def uncurry : (∀ i j, A i ⊗[ℂ] B j) ≃ₗ[ℂ] (∀ p : I × J, A p.1 ⊗[ℂ] B p.2) where
  toFun x p := x p.1 p.2
  invFun x i j := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates : ((∀ i, A i) ⊗[ℂ] (∀ j, B j)) ≃ₗ[ℂ]
    (∀ p : I × J, A p.1 ⊗[ℂ] B p.2) :=
  (TensorProduct.piLeft ℂ (∀ j, B j) A).trans
    ((LinearEquiv.piCongrRight (fun i => TensorProduct.piRight ℂ ℂ (A i) B)).trans uncurry)

@[simp] theorem coordinates_tmul (x : ∀ i, A i) (y : ∀ j, B j) (p : I × J) :
    coordinates (x ⊗ₜ[ℂ] y) p=x p.1 ⊗ₜ[ℂ] y p.2 := by
  simp [coordinates,uncurry,TensorProduct.piLeft,TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul]

variable (a : ∀ i, Representation ℂ G (A i)) (b : ∀ j, Representation ℂ H (B j))

def equivalence : Representation.Equiv (external (FiniteBlockHom.action a) (FiniteBlockHom.action b))
    (FiniteBlockHom.action (fun p : I × J => external (a p.1) (b p.2))) where
  toLinearEquiv := coordinates
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    funext p
    simp [external,Representation.tprod_apply]

end

noncomputable section
section Diagonal
variable {G I J : Type*} [Group G] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  {A : I → Type*} {B : J → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)]
  (a : ∀ i, Representation ℂ G (A i)) (b : ∀ j, Representation ℂ G (B j))

def diagonalEquivalence : Representation.Equiv
    ((FiniteBlockHom.action a).tprod (FiniteBlockHom.action b))
    (FiniteBlockHom.action (fun p : I × J => (a p.1).tprod (b p.2))) where
  toLinearEquiv := coordinates
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    funext p
    simp [Representation.tprod_apply]

end Diagonal

section Families
variable {G I : Type*} [Group G]
  {A B : I → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
  {a : ∀ i, Representation ℂ G (A i)} {b : ∀ i, Representation ℂ G (B i)}

def along (e : ∀ i, Representation.Equiv (a i) (b i)) :
    Representation.Equiv (FiniteBlockHom.action a) (FiniteBlockHom.action b) where
  toLinearEquiv := LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext i
    exact (e i).toIntertwiningMap.isIntertwining _ _ g (x i)

variable {J : I → Type*} {C : ∀ i, J i → Type*}
  [∀ i j, AddCommGroup (C i j)] [∀ i j, Module ℂ (C i j)]
  (c : ∀ i j, Representation ℂ G (C i j))

def flatten : Representation.Equiv (FiniteBlockHom.action (fun i => FiniteBlockHom.action (c i)))
    (FiniteBlockHom.action (fun p : Sigma J => c p.1 p.2)) where
  toLinearEquiv :=
    { toFun := fun x p => x p.1 p.2
      invFun := fun x i j => x ⟨i,j⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

end Families

end
end Math.FiniteExternalProducts
