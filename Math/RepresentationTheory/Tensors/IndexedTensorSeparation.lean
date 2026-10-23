import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic
import Math.RepresentationTheory.Invariants.MultilinearInvariantHom

/-! Heterogeneous finite tensor separation without finite-dimensional hypotheses. -/
namespace Math.IndexedTensorSeparation
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
  {L M : I → Type*} [∀ i, AddCommGroup (L i)] [∀ i, Module ℂ (L i)]
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def paired : MultilinearMap ℂ L
    (MultilinearMap ℂ M (⨂[ℂ] i, L i ⊗[ℂ] M i)) where
  toFun v := (PiTensorProduct.tprod ℂ).compLinearMap
    (fun i => TensorProduct.mk ℂ (L i) (M i) (v i))
  map_update_add' v i x y := by
    ext w
    change (PiTensorProduct.tprod ℂ) (fun j => Function.update v i (x+y) j ⊗ₜ[ℂ] w j) =
      (PiTensorProduct.tprod ℂ) (fun j => Function.update v i x j ⊗ₜ[ℂ] w j) +
        (PiTensorProduct.tprod ℂ) (fun j => Function.update v i y j ⊗ₜ[ℂ] w j)
    convert (PiTensorProduct.tprod ℂ).map_update_add
      (fun j => v j ⊗ₜ[ℂ] w j) i (x ⊗ₜ[ℂ] w i) (y ⊗ₜ[ℂ] w i) using 1 <;>
      congr 2 <;> funext j <;> by_cases h : j = i <;>
        subst_vars <;> simp_all [Function.update, TensorProduct.add_tmul]
  map_update_smul' v i z x := by
    ext w
    change (PiTensorProduct.tprod ℂ) (fun j => Function.update v i (z • x) j ⊗ₜ[ℂ] w j) =
      z • (PiTensorProduct.tprod ℂ) (fun j => Function.update v i x j ⊗ₜ[ℂ] w j)
    convert (PiTensorProduct.tprod ℂ).map_update_smul
      (fun j => v j ⊗ₜ[ℂ] w j) i z (x ⊗ₜ[ℂ] w i) using 1 <;>
      congr 2 <;> funext j <;> by_cases h : j = i <;>
        subst_vars <;> simp_all [Function.update, TensorProduct.smul_tmul']

def grouped : MultilinearMap ℂ L
    (MultilinearMap ℂ M ((⨂[ℂ] i, L i) ⊗[ℂ] (⨂[ℂ] i, M i))) where
  toFun v := (TensorProduct.mk ℂ (⨂[ℂ] i, L i) (⨂[ℂ] i, M i)
    (PiTensorProduct.tprod ℂ v)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  map_update_add' v i x y := by
    ext w
    change PiTensorProduct.tprod ℂ (Function.update v i (x+y)) ⊗ₜ[ℂ] _ = _
    rw [(PiTensorProduct.tprod ℂ).map_update_add, TensorProduct.add_tmul]
    rfl
  map_update_smul' v i z x := by
    ext w
    change PiTensorProduct.tprod ℂ (Function.update v i (z • x)) ⊗ₜ[ℂ] _ = _
    rw [(PiTensorProduct.tprod ℂ).map_update_smul, ← TensorProduct.smul_tmul']
    rfl

private def indexPairs {A B : I → Type*} :
    (∀ i, A i × B i) ≃ (∀ i, A i) × (∀ i, B i) where
  toFun p := (fun i => (p i).1, fun i => (p i).2)
  invFun q i := (q.1 i, q.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

private def ofBasis {A B : I → Type*} (l : ∀ i, Module.Basis (A i) ℂ (L i))
    (m : ∀ i, Module.Basis (B i) ℂ (M i)) : (⨂[ℂ] i, L i ⊗[ℂ] M i) ≃ₗ[ℂ]
    (⨂[ℂ] i, L i) ⊗[ℂ] (⨂[ℂ] i, M i) :=
  (Basis.piTensorProduct (fun i => (l i).tensorProduct (m i))).equiv
    ((Basis.piTensorProduct l).tensorProduct (Basis.piTensorProduct m)) indexPairs

omit [DecidableEq I] in
private theorem ofBasis_pure {A B : I → Type*} (l : ∀ i, Module.Basis (A i) ℂ (L i))
    (m : ∀ i, Module.Basis (B i) ℂ (M i)) (v : ∀ i, L i) (w : ∀ i, M i) :
    ofBasis l m (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i)) =
      PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w := by
  have he : ((ofBasis l m).toLinearMap.compMultilinearMapₗ ℂ).compMultilinearMap paired =
      grouped (L := L) (M := M) := by
    apply Module.Basis.ext_multilinear l
    intro a
    apply Module.Basis.ext_multilinear m
    intro b
    change ofBasis l m (PiTensorProduct.tprod ℂ (fun i => l i (a i) ⊗ₜ[ℂ] m i (b i))) = _
    let B := Basis.piTensorProduct (fun i => (l i).tensorProduct (m i))
    have hb : B (fun i => (a i, b i)) =
        PiTensorProduct.tprod ℂ (fun i => l i (a i) ⊗ₜ[ℂ] m i (b i)) := by
      simp only [B, Basis.piTensorProduct_apply, Module.Basis.tensorProduct_apply]
    rw [← hb]
    rw [ofBasis, Module.Basis.equiv_apply]
    simp [grouped, Module.Basis.tensorProduct_apply, Basis.piTensorProduct_apply,
      indexPairs]
  exact congrArg (fun f => f v w) he

/-- Internal basis choices prove existence; the generator formula fixes the map canonically. -/
def equiv : (⨂[ℂ] i, L i ⊗[ℂ] M i) ≃ₗ[ℂ]
    (⨂[ℂ] i, L i) ⊗[ℂ] (⨂[ℂ] i, M i) :=
  ofBasis (fun i => Module.Free.chooseBasis ℂ (L i))
    (fun i => Module.Free.chooseBasis ℂ (M i))

omit [DecidableEq I] in
theorem equiv_pure (v : ∀ i, L i) (w : ∀ i, M i) :
    equiv (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i)) =
      PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w :=
  ofBasis_pure _ _ v w

omit [DecidableEq I] in
theorem ext {N : Type*} [AddCommGroup N] [Module ℂ N]
    {f g : (⨂[ℂ] i, L i ⊗[ℂ] M i) →ₗ[ℂ] N}
    (he : ∀ (v : ∀ i, L i) (w : ∀ i, M i),
      f (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i)) =
      g (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i))) : f = g := by
  apply (Basis.piTensorProduct (fun i =>
    (Module.Free.chooseBasis ℂ (L i)).tensorProduct (Module.Free.chooseBasis ℂ (M i)))).ext
  intro x
  simp only [Basis.piTensorProduct_apply, Module.Basis.tensorProduct_apply']
  exact he _ _

def representationEquiv {G : Type*} [Group G]
    (a : ∀ i, Representation ℂ G (L i)) (b : ∀ i, Representation ℂ G (M i)) :
    Representation.Equiv (MultilinearInvariantHom.tensorRepresentation (fun i => (a i).tprod (b i)))
      ((MultilinearInvariantHom.tensorRepresentation a).tprod
        (MultilinearInvariantHom.tensorRepresentation b)) where
  toLinearEquiv := equiv
  isIntertwining' h := by
    apply ext
    intro v w
    change equiv ((MultilinearInvariantHom.tensorRepresentation
      (fun i => (a i).tprod (b i))) h (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i))) =
      ((MultilinearInvariantHom.tensorRepresentation a).tprod
        (MultilinearInvariantHom.tensorRepresentation b)) h
          (equiv (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i)))
    simp only [MultilinearInvariantHom.tensorRepresentation_tprod,
      Representation.tprod_apply, TensorProduct.map_tmul, equiv_pure]

omit [DecidableEq I] in
theorem equiv_unique (e : (⨂[ℂ] i, L i ⊗[ℂ] M i) ≃ₗ[ℂ]
    (⨂[ℂ] i, L i) ⊗[ℂ] (⨂[ℂ] i, M i))
    (he : ∀ (v : ∀ i, L i) (w : ∀ i, M i),
      e (PiTensorProduct.tprod ℂ (fun i => v i ⊗ₜ[ℂ] w i)) =
      PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ w) : e = equiv := by
  apply LinearEquiv.toLinearMap_injective
  apply ext
  intro v w
  exact (he v w).trans (equiv_pure v w).symm

end
end Math.IndexedTensorSeparation
