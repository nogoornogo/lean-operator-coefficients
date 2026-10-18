import Math.RepresentationTheory.IndexedTensorSeparation
import Math.RepresentationTheory.TypedMixedTensorHom

/-! Canonical local/multiplicity separation for both typed fermion and boson blocks. -/
namespace Math.MixedTensorSeparation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

section Tensor
variable {K A B C D A' B' : Type*} [Group K]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup A'] [Module ℂ A'] [AddCommGroup B'] [Module ℂ B']

theorem trivialTensor : (trivial ℂ K A).tprod (trivial ℂ K B) = trivial ℂ K (A ⊗[ℂ] B) := by
  ext k : 1
  apply TensorProduct.ext'
  intro x y
  rfl

def tensorCongr {a : Representation ℂ K A} {b : Representation ℂ K B}
    {a' : Representation ℂ K A'} {b' : Representation ℂ K B'}
    (e : Representation.Equiv a a') (f : Representation.Equiv b b') :
    Representation.Equiv (a.tprod b) (a'.tprod b') where
  toLinearEquiv := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  isIntertwining' := (e.toIntertwiningMap.tensor f.toIntertwiningMap).isIntertwining'

def shuffle (a : Representation ℂ K A) (b : Representation ℂ K B)
    (c : Representation ℂ K C) (d : Representation ℂ K D) :
    Representation.Equiv ((a.tprod b).tprod (c.tprod d)) ((a.tprod c).tprod (b.tprod d)) where
  toLinearEquiv := TensorProduct.tensorTensorTensorComm ℂ A B C D
  isIntertwining' k := by
    apply TensorProduct.ext_fourfold'
    intro x y z w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      Representation.tprod_apply, TensorProduct.map_tmul,
      TensorProduct.tensorTensorTensorComm_tmul]
end Tensor

variable {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Group K]
  {A B : I → Type*} {C D : J → Type*}
  [∀ i, AddCommGroup (A i)] [∀ i, Module ℂ (A i)]
  [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
  [∀ j, AddCommGroup (C j)] [∀ j, Module ℂ (C j)]
  [∀ j, AddCommGroup (D j)] [∀ j, Module ℂ (D j)]

abbrev Local := (⨂[ℂ] i, A i) ⊗[ℂ] (⨂[ℂ] j, C j)
abbrev Multiplicity := (⨂[ℂ] i, B i) ⊗[ℂ] (⨂[ℂ] j, D j)
abbrev Paired := (⨂[ℂ] i, A i ⊗[ℂ] B i) ⊗[ℂ] (⨂[ℂ] j, C j ⊗[ℂ] D j)

def equiv : Paired (A := A) (B := B) (C := C) (D := D) ≃ₗ[ℂ]
    Local (A := A) (C := C) ⊗[ℂ] Multiplicity (B := B) (D := D) :=
  (TensorProduct.congr IndexedTensorSeparation.equiv IndexedTensorSeparation.equiv).trans
    (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _)

omit [DecidableEq I] [DecidableEq J] [Group K] in
theorem equiv_pure (v : ∀ i, A i) (w : ∀ i, B i) (x : ∀ j, C j) (y : ∀ j, D j) :
    equiv (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun j => x j ⊗ₜ[ℂ] y j)) =
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ x) ⊗ₜ[ℂ]
        (PiTensorProduct.tprod ℂ w ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ y) := by
  simp only [equiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    IndexedTensorSeparation.equiv_pure, TensorProduct.tensorTensorTensorComm_tmul]

def representationEquiv (a : ∀ i, Representation ℂ K (A i)) (b : ∀ i, Representation ℂ K (B i))
    (c : ∀ j, Representation ℂ K (C j)) (d : ∀ j, Representation ℂ K (D j)) :
    Representation.Equiv
      ((MultilinearInvariantHom.tensorRepresentation (fun i => (a i).tprod (b i))).tprod
        (MultilinearInvariantHom.tensorRepresentation (fun j => (c j).tprod (d j))))
      (((MultilinearInvariantHom.tensorRepresentation a).tprod
        (MultilinearInvariantHom.tensorRepresentation c)).tprod
        ((MultilinearInvariantHom.tensorRepresentation b).tprod
          (MultilinearInvariantHom.tensorRepresentation d))) :=
  (tensorCongr (IndexedTensorSeparation.representationEquiv a b)
    (IndexedTensorSeparation.representationEquiv c d)).trans
    (shuffle (MultilinearInvariantHom.tensorRepresentation a)
      (MultilinearInvariantHom.tensorRepresentation b)
      (MultilinearInvariantHom.tensorRepresentation c)
      (MultilinearInvariantHom.tensorRepresentation d))

omit [DecidableEq I] [DecidableEq J] in
theorem representationEquiv_toLinearEquiv
    (a : ∀ i, Representation ℂ K (A i)) (b : ∀ i, Representation ℂ K (B i))
    (c : ∀ j, Representation ℂ K (C j)) (d : ∀ j, Representation ℂ K (D j)) :
    (representationEquiv a b c d).toLinearEquiv = equiv := rfl

omit [DecidableEq I] [DecidableEq J] in
theorem representationEquiv_toLinearMap
    (a : ∀ i, Representation ℂ K (A i)) (b : ∀ i, Representation ℂ K (B i))
    (c : ∀ j, Representation ℂ K (C j)) (d : ∀ j, Representation ℂ K (D j)) :
    (representationEquiv a b c d).toIntertwiningMap.toLinearMap = equiv.toLinearMap := rfl

end
end Math.MixedTensorSeparation
