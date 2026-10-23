import Math.RepresentationTheory.Constructions.MixedPowerDescent
import Math.RepresentationTheory.Symmetric.SymmetricMultilinearProjection
import Mathlib.LinearAlgebra.Multilinear.TensorProduct

namespace Math.SymmetricCoefficientDressing
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {B : Type*} [AddCommGroup B] [Module ℂ B] {p q : ℕ}

def raw (f : Sym[ℂ]^p B →ₗ[ℂ] ℂ) (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ) :
    MultilinearMap ℂ (fun _ : Fin (p+q) => B) ℂ :=
  ((TensorProduct.lift (LinearMap.mul ℂ ℂ)).compMultilinearMap
    ((f.compMultilinearMap (SymmetricPower.tprod ℂ)).domCoprod
      (g.compMultilinearMap (SymmetricPower.tprod ℂ)))).domDomCongr finSumFinEquiv

def rawLinear (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ) : (Sym[ℂ]^p B →ₗ[ℂ] ℂ) →ₗ[ℂ]
    MultilinearMap ℂ (fun _ : Fin (p+q) => B) ℂ where
  toFun f := raw f g
  map_add' f h := by
    ext w
    simp [raw,MultilinearMap.domDomCongr_apply,MultilinearMap.domCoprod_apply]
  map_smul' z f := by
    ext w
    simp [raw,MultilinearMap.domDomCongr_apply,MultilinearMap.domCoprod_apply,smul_eq_mul,mul_assoc]

def linear (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ) : (Sym[ℂ]^p B →ₗ[ℂ] ℂ) →ₗ[ℂ]
    (Sym[ℂ]^(p+q) B →ₗ[ℂ] ℂ) :=
  (SymmetricPowerDescent.equiv (p+q)).symm.toLinearMap.comp
    ((SymmetricMultilinearProjection.project (p+q)).comp (rawLinear g))

theorem diagonal (f : Sym[ℂ]^p B →ₗ[ℂ] ℂ) (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ) (x : B) :
    linear g f (SymmetricPower.tprod ℂ (fun _ => x)) =
      f (SymmetricPower.tprod ℂ (fun _ => x)) * g (SymmetricPower.tprod ℂ (fun _ => x)) := by
  change SymmetricPowerDescent.lift (p+q) _ (SymmetricPower.tprod ℂ (fun _ => x)) = _
  rw [SymmetricPowerDescent.lift_tprod]
  change SymmetricMultilinearProjection.raw (p+q) (raw f g) (fun _ => x) = _
  rw [SymmetricMultilinearProjection.raw_apply]
  simp only [raw,MultilinearMap.domDomCongr_apply,LinearMap.compMultilinearMap_apply,
    MultilinearMap.domCoprod_apply,LinearMap.compMultilinearMap_apply,TensorProduct.lift.tmul]
  simp only [Function.comp_def,smul_eq_mul,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_eq_mul]
  have hn : ((p+q).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (p+q)
  change (↑(p+q).factorial : ℂ)⁻¹ * (↑(p+q).factorial *
    (f (SymmetricPower.tprod ℂ (fun _ => x)) * g (SymmetricPower.tprod ℂ (fun _ => x)))) = _
  field_simp

theorem linear_apply (f : Sym[ℂ]^p B →ₗ[ℂ] ℂ) (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ)
    (w : Fin (p+q) → B) : linear g f (SymmetricPower.tprod ℂ w) =
    (Nat.factorial (p+q) : ℂ)⁻¹ * ∑ e : Equiv.Perm (Fin (p+q)),
      f (SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inl i))))) *
      g (SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inr i))))) := by
  change SymmetricPowerDescent.lift (p+q) _ (SymmetricPower.tprod ℂ w) = _
  rw [SymmetricPowerDescent.lift_tprod]
  change SymmetricMultilinearProjection.raw (p+q) (raw f g) w = _
  rw [SymmetricMultilinearProjection.raw_apply]
  rfl

variable {X : Type*} [AddCommGroup X] [Module ℂ X]
def productLinear (f : X ⊗[ℂ] Sym[ℂ]^p B →ₗ[ℂ] ℂ) (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ) :
    X ⊗[ℂ] Sym[ℂ]^(p+q) B →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((linear g).comp
    ((TensorProduct.lift.equiv (RingHom.id ℂ) X (Sym[ℂ]^p B) ℂ).symm f))

theorem productLinear_apply (f : X ⊗[ℂ] Sym[ℂ]^p B →ₗ[ℂ] ℂ) (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ)
    (x : X) (w : Fin (p+q) → B) : productLinear f g (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) =
    (Nat.factorial (p+q) : ℂ)⁻¹ * ∑ e : Equiv.Perm (Fin (p+q)),
      f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inl i))))) *
      g (SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inr i))))) := by
  exact linear_apply _ _ _

theorem productLinear_diagonal (f : X ⊗[ℂ] Sym[ℂ]^p B →ₗ[ℂ] ℂ) (g : Sym[ℂ]^q B →ₗ[ℂ] ℂ)
    (x : X) (w : B) : productLinear f g (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => w)) =
      f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => w)) *
      g (SymmetricPower.tprod ℂ (fun _ => w)) := by
  exact diagonal _ _ _

open Representation
variable {G : Type*} [Group G] (a : Representation ℂ G X) (b : Representation ℂ G B)
def product (f : IntertwiningMap (a.tprod (b.symmetricPower p)) (trivial ℂ G ℂ))
    (g : IntertwiningMap (b.symmetricPower q) (trivial ℂ G ℂ)) :
    IntertwiningMap (a.tprod (b.symmetricPower (p+q))) (trivial ℂ G ℂ) where
  toLinearMap := productLinear f.toLinearMap g.toLinearMap
  isIntertwining' u := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin (p+q)) B)
    rintro _ ⟨w,rfl⟩
    change productLinear f.toLinearMap g.toLinearMap
      (a u x ⊗ₜ[ℂ] b.symmetricPower (p+q) u (SymmetricPower.tprod ℂ w)) =
      productLinear f.toLinearMap g.toLinearMap (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w)
    rw [Representation.symmetricPower_apply_tprod,productLinear_apply,productLinear_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro e he
    have hf := IntertwiningMap.isIntertwining _ _ f u
      (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inl i)))))
    have hg := IntertwiningMap.isIntertwining _ _ g u
      (SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inr i)))))
    simp only [Representation.tprod_apply,TensorProduct.map_tmul,Representation.symmetricPower_apply_tprod,
      Representation.trivial_apply] at hf hg
    convert congrArg₂ (fun x y : ℂ => x*y) hf hg using 1

theorem product_diagonal (f : IntertwiningMap (a.tprod (b.symmetricPower p)) (trivial ℂ G ℂ))
    (g : IntertwiningMap (b.symmetricPower q) (trivial ℂ G ℂ)) (x : X) (w : B) :
    product a b f g (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => w)) =
      f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun _ => w)) *
      g (SymmetricPower.tprod ℂ (fun _ => w)) := productLinear_diagonal _ _ _ _


theorem product_apply (f : IntertwiningMap (a.tprod (b.symmetricPower p)) (trivial ℂ G ℂ))
    (g : IntertwiningMap (b.symmetricPower q) (trivial ℂ G ℂ)) (x : X) (w : Fin (p+q) → B) :
    product a b f g (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ w) =
    (Nat.factorial (p+q) : ℂ)⁻¹ * ∑ e : Equiv.Perm (Fin (p+q)),
      f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inl i))))) *
      g (SymmetricPower.tprod ℂ (fun i => w (e (finSumFinEquiv (Sum.inr i))))) := productLinear_apply _ _ _ _

end
end Math.SymmetricCoefficientDressing
