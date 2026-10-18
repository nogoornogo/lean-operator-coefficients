import Math.RepresentationTheory.SL2ClebschGordan
import Math.RepresentationTheory.MultilinearInvariantHom
import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-! Closure of symmetric-power spanning under tensors and equivariant quotients.
This supplies compact-to-complex invariance without computing multiplicities. -/
namespace Math.SL2SymmetricSpan
set_option autoImplicit false
noncomputable section
open Representation SL2SymmetricEmbeddings
open scoped TensorProduct
open scoped TensorPower
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

def generators (rho : Representation ℂ Group V) : Set V :=
  {v | ∃ (n : ℕ) (f : IntertwiningMap (doublet.symmetricPower n) rho)
    (x : Sym[ℂ]^n Doublet), f x = v}

def Spanned (rho : Representation ℂ Group V) : Prop :=
  Submodule.span ℂ (generators rho) = ⊤

theorem symmetricPower (n : ℕ) : Spanned (doublet.symmetricPower n) := by
  apply top_unique
  intro x hx
  exact Submodule.subset_span ⟨n, IntertwiningMap.id _, x, rfl⟩

theorem of_surjective (rho : Representation ℂ Group V) (sigma : Representation ℂ Group W)
    (q : IntertwiningMap rho sigma) (hq : Function.Surjective q) (hr : Spanned rho) :
    Spanned sigma := by
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨x,rfl⟩ := hq y
  have hx : x ∈ Submodule.span ℂ (generators rho) := by rw [hr]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,f,v,rfl⟩ := hx
    exact Submodule.subset_span ⟨n,q.comp f,v,rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem tensor (rho : Representation ℂ Group V) (sigma : Representation ℂ Group W)
    (hr : Spanned rho) (hs : Spanned sigma) : Spanned (rho.tprod sigma) := by
  let S := Submodule.span ℂ (generators (rho.tprod sigma))
  have hgen {x : V} {y : W} (hx : x ∈ generators rho) (hy : y ∈ generators sigma) :
      x ⊗ₜ[ℂ] y ∈ S := by
    obtain ⟨h,f,v,rfl⟩ := hx
    obtain ⟨d,g,w,rfl⟩ := hy
    obtain ⟨a,ha⟩ := (SL2ClebschGordan.equivalence h d).surjective (v ⊗ₜ[ℂ] w)
    have he : f v ⊗ₜ[ℂ] g w =
        ∑ r, ((f.tensor g).comp (SL2ClebschGordan.embed h d r)) (a r) := by
      change (f.tensor g) (v ⊗ₜ[ℂ] w) = _
      rw [← ha]
      change (f.tensor g) (SL2ClebschGordan.assemble h d a) = _
      simp only [SL2ClebschGordan.assemble, DistinctIrreducibleAssembly.assemble_apply,
        map_sum, IntertwiningMap.comp_apply]
    rw [he]
    exact Submodule.sum_mem S (fun r _ => Submodule.subset_span
      ⟨SL2ClebschGordan.degree h d r,
        (f.tensor g).comp (SL2ClebschGordan.embed h d r),a r,rfl⟩)
  have hp (x : V) (y : W) : x ⊗ₜ[ℂ] y ∈ S := by
    have hx : x ∈ Submodule.span ℂ (generators rho) := by rw [hr]; trivial
    have hy : y ∈ Submodule.span ℂ (generators sigma) := by rw [hs]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      induction hy using Submodule.span_induction with
      | mem y hy => exact hgen hx hy
      | zero => simp
      | add y z _ _ hy hz => simpa [TensorProduct.tmul_add] using S.add_mem hy hz
      | smul c y _ hy => simpa [TensorProduct.tmul_smul] using S.smul_mem c hy
    | zero => simp
    | add x z _ _ hx hz => simpa [TensorProduct.add_tmul] using S.add_mem hx hz
    | smul c x _ hx => simpa [← TensorProduct.smul_tmul'] using S.smul_mem c hx
  apply top_unique
  intro x hx
  clear hx
  change x ∈ S
  induction x using TensorProduct.inductionOn with
  | tmul x y => exact hp x y
  | add x y hx hy => exact S.add_mem hx hy

theorem standard : Spanned doublet :=
  of_surjective _ _ (SymmetricPowerLowDegree.representationOneEquiv doublet).toIntertwiningMap
    (SymmetricPowerLowDegree.representationOneEquiv doublet).surjective (symmetricPower 1)

theorem trivial : Spanned (Representation.trivial ℂ Group V) := by
  apply top_unique
  intro x hx
  let q : IntertwiningMap (doublet.symmetricPower 0) (Representation.trivial ℂ Group V) :=
    { toLinearMap := (SymmetricPowerLowDegree.zeroEvaluation).smulRight x
      isIntertwining' g := by
        apply SymmetricPower.ext
        intro v
        simp }
  exact Submodule.subset_span ⟨0, q,
    SymmetricPower.tprod ℂ (fun i : Fin 0 => Fin.elim0 i), by simp [q]⟩

abbrev power (rho : Representation ℂ Group V) (n : ℕ) :=
  MultilinearInvariantHom.tensorRepresentation (fun _ : Fin n => rho)

def successor (n : ℕ) : ((⨂[ℂ]^n V) ⊗[ℂ] V) ≃ₗ[ℂ] (⨂[ℂ]^(n+1) V) :=
  (TensorProduct.congr (LinearEquiv.refl ℂ _)
    (PiTensorProduct.subsingletonEquiv (R := ℂ) (s := fun _ : Fin 1 => V) 0).symm).trans
    ((PiTensorProduct.tmulEquiv ℂ V).trans
      (PiTensorProduct.reindex ℂ (fun _ : Fin n ⊕ Fin 1 => V) finSumFinEquiv))

@[simp] theorem successor_tmul (n : ℕ) (v : Fin n → V) (w : V) :
    successor n (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] w) =
      PiTensorProduct.tprod ℂ (fun i => Sum.elim v (fun _ => w) (finSumFinEquiv.symm i)) := by
  simp [successor, PiTensorProduct.subsingletonEquiv_symm_apply',
    PiTensorProduct.tmulEquiv_apply, PiTensorProduct.reindex_tprod]

def successorMap (rho : Representation ℂ Group V) (n : ℕ) :
    IntertwiningMap ((power rho n).tprod rho) (power rho (n+1)) where
  toLinearMap := (successor n).toLinearMap
  isIntertwining' g := by
    apply TensorProduct.ext
    apply PiTensorProduct.ext
    ext v w
    change successor n ((power rho n) g (PiTensorProduct.tprod ℂ v) ⊗ₜ[ℂ] rho g w) =
      power rho (n+1) g (successor n (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] w))
    simp only [MultilinearInvariantHom.tensorRepresentation_tprod, successor_tmul]
    congr 1
    funext i
    cases finSumFinEquiv.symm i <;> rfl

theorem tensorPower (rho : Representation ℂ Group V) (hr : Spanned rho) (n : ℕ) :
    Spanned (power rho n) := by
  induction n with
  | zero =>
    have he : power rho 0 = Representation.trivial ℂ Group (⨂[ℂ]^0 V) := by
      have hf : (fun _ : Fin 0 => rho) =
          (fun _ : Fin 0 => Representation.trivial ℂ Group V) := by funext i; exact Fin.elim0 i
      unfold power
      rw [hf, MultilinearInvariantHom.tensorRepresentation_trivial]
    rw [he]
    exact trivial
  | succ n ih =>
    exact of_surjective _ _ (successorMap rho n) (successor n).surjective
      (tensor _ _ ih hr)

def exteriorMap (rho : Representation ℂ Group V) (n : ℕ) :
    IntertwiningMap (power rho n) (rho.exteriorPower n) where
  toLinearMap := _root_.exteriorPower.fromTensorPower ℂ V n
  isIntertwining' g := by
    apply PiTensorProduct.ext
    ext v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      MultilinearInvariantHom.tensorRepresentation_tprod,
      _root_.exteriorPower.fromTensorPower_tprod, Representation.exteriorPower_apply_ιMulti]
    rfl

theorem exterior (rho : Representation ℂ Group V) (hr : Spanned rho) (n : ℕ) :
    Spanned (rho.exteriorPower n) :=
  of_surjective _ _ (exteriorMap rho n) (_root_.exteriorPower.fromTensorPower_surjective n)
    (tensorPower rho hr n)

theorem coefficient_fixed_of_compact (rho : Representation ℂ Group V) (hr : Spanned rho)
    (f : V →ₗ[ℂ] ℂ) (hc : ∀ u x, f (rho (compactInclusion u) x) = f x) :
    ∀ g x, f (rho g x) = f x := by
  intro g x
  have hx : x ∈ Submodule.span ℂ (generators rho) := by rw [hr]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n,q,v,rfl⟩ := hx
    have he := SL2SymmetricEmbeddings.coefficient_fixed_of_compact n
      (f.comp q.toLinearMap) (fun u y => by
        change f (q ((doublet.symmetricPower n) (compactInclusion u) y)) = f (q y)
        rw [q.isIntertwining _ _ (compactInclusion u)]
        exact hc u (q y)) g v
    change f (q ((doublet.symmetricPower n) g v)) = f (q v) at he
    rw [q.isIntertwining _ _ g] at he
    exact he
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [map_smul, hx]

end
end Math.SL2SymmetricSpan
