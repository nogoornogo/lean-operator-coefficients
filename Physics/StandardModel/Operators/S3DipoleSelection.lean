import Physics.StandardModel.Operators.DipoleFlavorSelection
import Mathlib.GroupTheory.Perm.Fin

namespace GUT.S3DipoleSelection
set_option autoImplicit false
noncomputable section
open Representation
abbrev H := Equiv.Perm (Fin 3)
abbrev V := Fin 3 → ℂ

def action : Representation ℂ H V where
  toFun g :=
    { toFun := fun x i => x (g⁻¹ i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext; rfl
  map_mul' g h := by ext; rfl

@[simp] theorem action_apply (g : H) (x : V) (i : Fin 3) : action g x i = x (g⁻¹ i) := rfl

theorem noncommuting : (Equiv.swap (0 : Fin 3) 1) * Equiv.swap 1 2 ≠
    (Equiv.swap (1 : Fin 3) 2) * Equiv.swap 0 1 := by decide +kernel

theorem generator_relations :
    (Equiv.swap (0 : Fin 3) 1)^2 = 1 ∧ (Equiv.swap (1 : Fin 3) 2)^2 = 1 ∧
      ((Equiv.swap (0 : Fin 3) 1)*Equiv.swap 1 2)^3 = 1 := by decide +kernel

theorem normal_forms : ∀ g : H,
    let s := Equiv.swap (0 : Fin 3) 1
    let t := Equiv.swap (1 : Fin 3) 2
    g=1 ∨ g=s ∨ g=t ∨ g=s*t ∨ g=t*s ∨ g=s*t*s := by decide +kernel

def ones : V := fun _ => 1

def sumMap : IntertwiningMap action action where
  toLinearMap :=
    { toFun := fun x _ => ∑ i, x i
      map_add' := by intro x y; ext; simp [Finset.sum_add_distrib]
      map_smul' := by intro z x; ext; simp [Finset.mul_sum] }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    funext i
    change (∑ j, x (g⁻¹ j)) = ∑ j, x j
    exact Equiv.sum_comp g⁻¹ x

theorem action_single (g : H) (i : Fin 3) :
    action g (Pi.single i 1) = Pi.single (g i) 1 := by
  ext j
  simp only [action_apply,Pi.single_apply]
  have he : g⁻¹ j = i ↔ j = g i := by
    constructor
    · intro h; simpa using congrArg g h
    · rintro rfl; simp
  change g.symm j = i ↔ j = g i at he
  change (if g.symm j = i then (1 : ℂ) else 0) = if j = g i then 1 else 0
  simp only [he]

theorem entry_equivariant (f : IntertwiningMap action action) (g : H) (i j : Fin 3) :
    f (Pi.single (g i) 1) (g j) = f (Pi.single i 1) j := by
  have he := congrArg (fun x => x (g j))
    (IntertwiningMap.isIntertwining _ _ f g (Pi.single i 1))
  simpa [action_single] using he

theorem entries (f : IntertwiningMap action action) (i j : Fin 3) :
    f (Pi.single i 1) j =
      if i=j then f (Pi.single 0 1) 0 else f (Pi.single 0 1) 1 := by
  have h01 := entry_equivariant f (Equiv.swap (0 : Fin 3) 1)
  have h12 := entry_equivariant f (Equiv.swap (1 : Fin 3) 2)
  have h02 := entry_equivariant f (Equiv.swap (0 : Fin 3) 2)
  have h0100 := h01 0 0
  have h0101 := h01 0 1
  have h0102 := h01 0 2
  have h0110 := h01 1 0
  have h0111 := h01 1 1
  have h0112 := h01 1 2
  have h0120 := h01 2 0
  have h0121 := h01 2 1
  have h0122 := h01 2 2
  have h1200 := h12 0 0
  have h1201 := h12 0 1
  have h1202 := h12 0 2
  have h1210 := h12 1 0
  have h1211 := h12 1 1
  have h1212 := h12 1 2
  have h1220 := h12 2 0
  have h1221 := h12 2 1
  have h1222 := h12 2 2
  have h0200 := h02 0 0
  have h0201 := h02 0 1
  have h0202 := h02 0 2
  have h0210 := h02 1 0
  have h0211 := h02 1 1
  have h0212 := h02 1 2
  have h0220 := h02 2 0
  have h0221 := h02 2 1
  have h0222 := h02 2 2
  fin_cases i <;> fin_cases j <;> simp_all [Equiv.swap_apply_def]

theorem centralizer (f : IntertwiningMap action action) (x : V) :
    f x = (f (Pi.single 0 1) 0 - f (Pi.single 0 1) 1) • x +
      f (Pi.single 0 1) 1 • sumMap x := by
  have hx : x = ∑ i, x i • Pi.single i 1 := by ext t; simp [Pi.single_apply]
  conv_lhs => rw [hx,map_sum]
  simp only [map_smul]
  ext j
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.add_apply]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change x 0 * f (Pi.single 0 1) j +
    (x 1 * f (Pi.single 1 1) j + x 2 * f (Pi.single 2 1) j) = _
  rw [entries f 0 j,entries f 1 j,entries f 2 j]
  fin_cases j <;> simp [Fin.sum_univ_succ,sumMap] <;> ring

theorem selected_allowed_iff (mu : V) (ell : Module.Dual ℂ V) :
    (∃ c : DipoleFlavorSelection.Coefficients action action,
      DipoleFlavorSelection.selector action action mu ell c ≠ 0) ↔
    ell mu ≠ 0 ∨ (∑ i, mu i) * ell ones ≠ 0 := by
  rw [DipoleFlavorSelection.allowed_iff]
  constructor
  · rintro ⟨f,hf⟩
    by_contra hn
    have hz : ell mu = 0 ∧ (∑ i, mu i)*ell ones = 0 := by simpa only [not_or,not_not] using hn
    apply hf
    rw [centralizer f mu,map_add,map_smul,map_smul]
    have hs : sumMap mu = (∑ i, mu i) • ones := by ext; simp [sumMap,ones]
    rw [hs,map_smul]
    simp only [smul_eq_mul]
    rw [hz.1,mul_zero,zero_add,← mul_assoc]
    simp [mul_assoc,hz.2]
  · rintro (h | h)
    · exact ⟨IntertwiningMap.id action,h⟩
    · refine ⟨sumMap,?_⟩
      have hs : sumMap mu = (∑ i, mu i) • ones := by ext; simp [sumMap,ones]
      simpa [hs] using h

theorem selected_forbidden_iff (mu : V) (ell : Module.Dual ℂ V) :
    (∀ c : DipoleFlavorSelection.Coefficients action action,
      DipoleFlavorSelection.selector action action mu ell c = 0) ↔
    ell mu = 0 ∧ (∑ i, mu i)*ell ones = 0 := by
  classical
  simpa only [not_exists,not_not,not_or] using not_congr (selected_allowed_iff mu ell)

theorem off_diagonal_allowed :
    ∃ c : DipoleFlavorSelection.Coefficients action action,
      DipoleFlavorSelection.selector action action (Pi.single 0 1) (LinearMap.proj 1) c ≠ 0 := by
  apply (selected_allowed_iff _ _).mpr
  right
  simp [ones]
end
end GUT.S3DipoleSelection
