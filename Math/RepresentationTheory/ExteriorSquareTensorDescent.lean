import Math.RepresentationTheory.TensorSquareMultilinear
import TauCeti.RepresentationTheory.ExteriorPower

/-! Antisymmetric tensor coefficients descend to the independent exterior square. -/
namespace Math.ExteriorSquareTensorDescent
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {A N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup N] [Module ℂ N]

abbrev antisymmetric : Submodule ℂ ((A ⊗[ℂ] A) →ₗ[ℂ] N) where
  carrier := {f | ∀ x y, f (y ⊗ₜ[ℂ] x) = -f (x ⊗ₜ[ℂ] y)}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x y; change f _ + g _ = -(f _ + g _); rw [hf, hg, neg_add]
  smul_mem' := by intro z f hf x y; change z • f _ = -(z • f _); rw [hf, smul_neg]

def alternating (f : antisymmetric (A := A) (N := N)) : A [⋀^Fin 2]→ₗ[ℂ] N where
  toMultilinearMap := TensorSquareMultilinear.toMultilinear f.val
  map_eq_zero_of_eq' v i j hij hne := by
    have hv : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    change f.val (v 0 ⊗ₜ[ℂ] v 1) = 0
    rw [hv]
    have h := f.property (v 1) (v 1)
    have h2 : (2 : ℂ) • f.val (v 1 ⊗ₜ[ℂ] v 1) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp h
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

def wedge : (A ⊗[ℂ] A) →ₗ[ℂ] (⋀[ℂ]^2 A) :=
  TensorSquareMultilinear.fromMultilinear (exteriorPower.ιMulti ℂ 2).toMultilinearMap

@[simp] theorem wedge_tmul (x y : A) : wedge (x ⊗ₜ[ℂ] y) =
    exteriorPower.ιMulti ℂ 2 ![x,y] := rfl

theorem wedge_swap (x y : A) : wedge (y ⊗ₜ[ℂ] x) = -wedge (x ⊗ₜ[ℂ] y) := by
  have h := (exteriorPower.ιMulti ℂ 2 (M := A)).map_swap ![x,y] (by decide : (0 : Fin 2) ≠ 1)
  have hv : (![x,y] : Fin 2 → A) ∘ Equiv.swap 0 1 = ![y,x] := by
    ext i
    fin_cases i <;> simp
  simpa only [hv, wedge_tmul] using h

def equiv : antisymmetric (A := A) (N := N) ≃ₗ[ℂ] ((⋀[ℂ]^2 A) →ₗ[ℂ] N) where
  toFun f := exteriorPower.alternatingMapLinearEquiv (alternating f)
  invFun f := ⟨f.comp wedge, by
    intro x y
    change f (wedge (y ⊗ₜ[ℂ] x)) = -f (wedge (x ⊗ₜ[ℂ] y))
    rw [wedge_swap, map_neg]⟩
  left_inv f := by
    apply Subtype.ext
    ext x y
    change exteriorPower.alternatingMapLinearEquiv (alternating f)
      (exteriorPower.ιMulti ℂ 2 ![x,y]) = f.val (x ⊗ₜ[ℂ] y)
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  right_inv f := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply]
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change f (exteriorPower.ιMulti ℂ 2 ![v 0,v 1]) = f (exteriorPower.ιMulti ℂ 2 v)
    congr 2
  map_add' f g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearMap.add_apply]
    rfl
  map_smul' z f := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, LinearMap.smul_apply]
    rfl

@[simp] theorem equiv_apply (f : antisymmetric (A := A) (N := N)) (v : Fin 2 → A) :
    equiv f (exteriorPower.ιMulti ℂ 2 v) = f.val (v 0 ⊗ₜ[ℂ] v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

section Tensor
variable {B : Type*} [AddCommGroup B] [Module ℂ B]

abbrev tensorAntisymmetric : Submodule ℂ (((A ⊗[ℂ] A) ⊗[ℂ] B) →ₗ[ℂ] N) where
  carrier := {f | ∀ x y b, f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] b) = -f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] b)}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x y b; change f _ + g _ = -(f _ + g _); rw [hf, hg, neg_add]
  smul_mem' := by intro z f hf x y b; change z • f _ = -(z • f _); rw [hf, smul_neg]

def curryEquiv : tensorAntisymmetric (A := A) (B := B) (N := N) ≃ₗ[ℂ]
    antisymmetric (A := A) (N := B →ₗ[ℂ] N) where
  toFun f := ⟨TensorProduct.curry f.val, by
    intro x y
    ext b
    exact f.property x y b⟩
  invFun f := ⟨TensorProduct.lift f.val, by
    intro x y b
    exact LinearMap.congr_fun (f.property x y) b⟩
  left_inv f := by apply Subtype.ext; ext x b; rfl
  right_inv f := by apply Subtype.ext; ext x b; rfl
  map_add' f g := by apply Subtype.ext; ext x b; rfl
  map_smul' z f := by apply Subtype.ext; ext x b; rfl

def tensorEquiv : tensorAntisymmetric (A := A) (B := B) (N := N) ≃ₗ[ℂ]
    (((⋀[ℂ]^2 A) ⊗[ℂ] B) →ₗ[ℂ] N) :=
  curryEquiv.trans (equiv.trans (TensorProduct.lift.equiv (RingHom.id ℂ) _ _ _))

@[simp] theorem tensorEquiv_apply
    (f : tensorAntisymmetric (A := A) (B := B) (N := N)) (v : Fin 2 → A) (b : B) :
    tensorEquiv f (exteriorPower.ιMulti ℂ 2 v ⊗ₜ[ℂ] b) =
      f.val ((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] b) := by
  change equiv (curryEquiv f) (exteriorPower.ιMulti ℂ 2 v) b = _
  rw [equiv_apply]
  rfl

@[simp] theorem tensorEquiv_symm_apply
    (f : ((⋀[ℂ]^2 A) ⊗[ℂ] B) →ₗ[ℂ] N) (x y : A) (b : B) :
    (tensorEquiv.symm f).val ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] b) =
      f (exteriorPower.ιMulti ℂ 2 ![x,y] ⊗ₜ[ℂ] b) := rfl

end Tensor

section Equivariant
open Representation
variable {R B : Type*} [Group R] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ R A) (b : Representation ℂ R B) (n : Representation ℂ R N)

abbrev tensorIntertwiners : Submodule ℂ (IntertwiningMap ((a.tprod a).tprod b) n) where
  carrier := {f | ∀ x y z, f ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] z) = -f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x y z; change f _ + g _ = -(f _ + g _); rw [hf, hg, neg_add]
  smul_mem' := by intro c f hf x y z; change c • f _ = -(c • f _); rw [hf, smul_neg]

def descend (f : tensorIntertwiners a b n) :
    IntertwiningMap ((a.exteriorPower 2).tprod b) n where
  toLinearMap := tensorEquiv ⟨f.val.toLinearMap, f.property⟩
  isIntertwining' r := by
    apply TensorProduct.ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext
    intro z
    change tensorEquiv ⟨f.val.toLinearMap, f.property⟩
      ((a.exteriorPower 2) r (exteriorPower.ιMulti ℂ 2 v) ⊗ₜ[ℂ] b r z) =
      n r (tensorEquiv ⟨f.val.toLinearMap, f.property⟩ (exteriorPower.ιMulti ℂ 2 v ⊗ₜ[ℂ] z))
    rw [Representation.exteriorPower_apply_ιMulti, tensorEquiv_apply, tensorEquiv_apply]
    exact IntertwiningMap.isIntertwining _ _ f.val r ((v 0 ⊗ₜ[ℂ] v 1) ⊗ₜ[ℂ] z)

def restrict (f : IntertwiningMap ((a.exteriorPower 2).tprod b) n) :
    tensorIntertwiners a b n :=
  ⟨{ toLinearMap := (tensorEquiv.symm f.toLinearMap).val
     isIntertwining' r := by
       apply TensorProduct.ext'
       intro xy z
       induction xy using TensorProduct.inductionOn with
       | add x y hx hy => simp_all [TensorProduct.add_tmul]
       | tmul x y =>
         change f (exteriorPower.ιMulti ℂ 2 ![a r x,a r y] ⊗ₜ[ℂ] b r z) =
           n r (f (exteriorPower.ιMulti ℂ 2 ![x,y] ⊗ₜ[ℂ] z))
         have hv : ![a r x,a r y] = a r ∘ ![x,y] := by ext i; fin_cases i <;> rfl
         rw [hv, ← Representation.exteriorPower_apply_ιMulti]
         exact IntertwiningMap.isIntertwining _ _ f r
           (exteriorPower.ιMulti ℂ 2 ![x,y] ⊗ₜ[ℂ] z) },
    (tensorEquiv.symm f.toLinearMap).property⟩

def equivariantEquiv : tensorIntertwiners a b n ≃ₗ[ℂ]
    IntertwiningMap ((a.exteriorPower 2).tprod b) n where
  toFun := descend a b n
  invFun := restrict a b n
  left_inv f := by
    apply Subtype.ext
    apply IntertwiningMap.ext
    exact congrArg Subtype.val (tensorEquiv.symm_apply_apply ⟨f.val.toLinearMap, f.property⟩)
  right_inv f := by
    apply IntertwiningMap.ext
    exact tensorEquiv.apply_symm_apply f.toLinearMap
  map_add' f g := by
    apply IntertwiningMap.ext
    exact tensorEquiv.map_add ⟨f.val.toLinearMap, f.property⟩ ⟨g.val.toLinearMap, g.property⟩
  map_smul' z f := by
    apply IntertwiningMap.ext
    exact tensorEquiv.map_smul z ⟨f.val.toLinearMap, f.property⟩

end Equivariant

end
end Math.ExteriorSquareTensorDescent
