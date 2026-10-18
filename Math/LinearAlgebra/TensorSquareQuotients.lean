import Math.RepresentationTheory.ExteriorSquareTensorDescent
import Math.RepresentationTheory.SymmetricPowerDescent

/-! Basis-free square quotients and their unnormalized sections. -/
namespace Math.TensorSquareQuotients
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
@[reducible] local instance (V W : Type*) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] : AddCommGroup (V ⊗[ℂ] W) := inferInstance

variable {A N : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup N] [Module ℂ N]

abbrev wedge := ExteriorSquareTensorDescent.wedge (A := A)

def sym : (A ⊗[ℂ] A) →ₗ[ℂ] Sym[ℂ]^2 A :=
  TensorSquareMultilinear.fromMultilinear (SymmetricPower.tprod ℂ)

@[simp] theorem sym_tmul (x y : A) : sym (x ⊗ₜ[ℂ] y)=SymmetricPower.tprod ℂ ![x,y] := rfl

theorem sym_swap (x y : A) : sym (y ⊗ₜ[ℂ] x)=sym (x ⊗ₜ[ℂ] y) := by
  have h := SymmetricPower.tprod_equiv (R := ℂ) (Equiv.swap (0 : Fin 2) 1) ![x,y]
  change SymmetricPower.tprod ℂ ![y,x]=SymmetricPower.tprod ℂ ![x,y]
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

def symmetricLift (f : (A ⊗[ℂ] A) →ₗ[ℂ] N)
    (hf : ∀ x y, f (y ⊗ₜ[ℂ] x)=f (x ⊗ₜ[ℂ] y)) : Sym[ℂ]^2 A →ₗ[ℂ] N :=
  SymmetricPowerDescent.lift 2 ⟨TensorSquareMultilinear.toMultilinear f,by
    intro e v
    rcases TauCeti.perm_fin_two_eq_one_or_swap e with rfl | rfl
    · rfl
    · exact hf (v 0) (v 1)⟩

@[simp] theorem symmetricLift_pure (f : (A ⊗[ℂ] A) →ₗ[ℂ] N)
    (hf : ∀ x y, f (y ⊗ₜ[ℂ] x)=f (x ⊗ₜ[ℂ] y)) (x y : A) :
    symmetricLift f hf (sym (x ⊗ₜ[ℂ] y))=f (x ⊗ₜ[ℂ] y) :=
  SymmetricPowerDescent.lift_tprod _ _ _

def symmetricSection : Sym[ℂ]^2 A →ₗ[ℂ] A ⊗[ℂ] A :=
  symmetricLift (LinearMap.id+(TensorProduct.comm ℂ A A).toLinearMap)
    (by intro x y; simp [add_comm])

def alternatingSection : (⋀[ℂ]^2 A) →ₗ[ℂ] A ⊗[ℂ] A :=
  ExteriorSquareTensorDescent.equiv
    ⟨LinearMap.id-(TensorProduct.comm ℂ A A).toLinearMap,by
      intro x y
      simp [neg_sub]⟩

@[simp] theorem symmetricSection_pure (x y : A) :
    symmetricSection (sym (x ⊗ₜ[ℂ] y))=x ⊗ₜ[ℂ] y+y ⊗ₜ[ℂ] x := by
  exact symmetricLift_pure _ _ x y

@[simp] theorem alternatingSection_pure (x y : A) :
    alternatingSection (wedge (x ⊗ₜ[ℂ] y))=x ⊗ₜ[ℂ] y-y ⊗ₜ[ℂ] x := by
  rw [alternatingSection,ExteriorSquareTensorDescent.wedge_tmul,
    ExteriorSquareTensorDescent.equiv_apply]
  rfl

theorem sym_eta (v : Fin 2 → A) : sym (v 0 ⊗ₜ[ℂ] v 1)=SymmetricPower.tprod ℂ v := by
  change SymmetricPower.tprod ℂ ![v 0,v 1]=SymmetricPower.tprod ℂ v
  congr 1
  ext i
  fin_cases i <;> rfl

theorem wedge_eta (v : Fin 2 → A) : wedge (v 0 ⊗ₜ[ℂ] v 1)=exteriorPower.ιMulti ℂ 2 v := by
  rw [ExteriorSquareTensorDescent.wedge_tmul]
  congr 1
  ext i
  fin_cases i <;> rfl

theorem sym_section (x : Sym[ℂ]^2 A) : sym (symmetricSection x)=(2 : ℂ) • x := by
  have h : (sym (A := A)).comp (symmetricSection (A := A))=(2 : ℂ) • LinearMap.id := by
    apply SymmetricPower.ext
    intro v
    change sym (symmetricSection (sym (v 0 ⊗ₜ[ℂ] v 1)))=_
    change sym (symmetricSection (sym (v 0 ⊗ₜ[ℂ] v 1)))=(2 : ℂ) • SymmetricPower.tprod ℂ v
    rw [symmetricSection_pure,map_add,sym_swap (v 0) (v 1),sym_eta,two_smul]
  exact LinearMap.congr_fun h x

theorem wedge_section (x : ⋀[ℂ]^2 A) : wedge (alternatingSection x)=(2 : ℂ) • x := by
  have h : (wedge (A := A)).comp (alternatingSection (A := A))=(2 : ℂ) • LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change wedge (alternatingSection (wedge (v 0 ⊗ₜ[ℂ] v 1)))=_
    change wedge (alternatingSection (wedge (v 0 ⊗ₜ[ℂ] v 1)))=(2 : ℂ) • exteriorPower.ιMulti ℂ 2 v
    rw [alternatingSection_pure,map_sub,ExteriorSquareTensorDescent.wedge_swap (v 0) (v 1),
      sub_neg_eq_add,wedge_eta,two_smul]
  exact LinearMap.congr_fun h x

theorem sym_alternating (x : ⋀[ℂ]^2 A) : sym (alternatingSection x)=0 := by
  have h : (sym (A := A)).comp (alternatingSection (A := A))=0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change sym (alternatingSection (wedge (v 0 ⊗ₜ[ℂ] v 1)))=0
    rw [alternatingSection_pure,map_sub,sym_swap (v 0) (v 1),sub_self]
  exact LinearMap.congr_fun h x

theorem wedge_symmetric (x : Sym[ℂ]^2 A) : wedge (symmetricSection x)=0 := by
  have h : (wedge (A := A)).comp (symmetricSection (A := A))=0 := by
    apply SymmetricPower.ext
    intro v
    change wedge (symmetricSection (sym (v 0 ⊗ₜ[ℂ] v 1)))=0
    rw [symmetricSection_pure,map_add,ExteriorSquareTensorDescent.wedge_swap (v 0) (v 1),add_neg_cancel]
  exact LinearMap.congr_fun h x

end
end Math.TensorSquareQuotients
