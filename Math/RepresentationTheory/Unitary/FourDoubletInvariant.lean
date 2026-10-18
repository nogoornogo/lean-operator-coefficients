import Math.RepresentationTheory.Unitary.SmallSpecialUnitary
import Math.RepresentationTheory.FourTensorMultilinear
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Four defining SU(2) doublets: two epsilon products exhaust invariants.
One diagonal phase removes unbalanced coordinates, the signed flip pairs the
six balanced coordinates, and one rotation supplies their single relation. -/
namespace Math.FourDoubletInvariant
set_option autoImplicit false
noncomputable section
open Matrix SmallSpecialUnitary
open scoped TensorProduct
abbrev Space := Fin 2 → ℂ
abbrev Group := specialUnitaryGroup (Fin 2) ℂ
abbrev Tensor := (Space ⊗[ℂ] Space) ⊗[ℂ] (Space ⊗[ℂ] Space)
abbrev Coefficient := Tensor →ₗ[ℂ] ℂ
def IsInvariant (f : Coefficient) : Prop := ∀ (g : Group) a b c d,
  f ((defining 2 g a ⊗ₜ[ℂ] defining 2 g b) ⊗ₜ[ℂ]
    (defining 2 g c ⊗ₜ[ℂ] defining 2 g d)) = f ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d))
def basis (i : Fin 2) : Space := Pi.single i 1
def value (f : Coefficient) (i j k l : Fin 2) :=
  f ((basis i ⊗ₜ[ℂ] basis j) ⊗ₜ[ℂ] (basis k ⊗ₜ[ℂ] basis l))
private theorem value_eq (f : Coefficient) (i j k l : Fin 2) :
    value f i j k l = f ((basis i ⊗ₜ[ℂ] basis j) ⊗ₜ[ℂ] (basis k ⊗ₜ[ℂ] basis l)) := rfl
def Balanced (i j k l : Fin 2) : Prop := i.val + j.val + k.val + l.val = 2

private def phase : Group :=
  ⟨!![(3 + 4 * Complex.I) / 5, 0; 0, (3 - 4 * Complex.I) / 5], by
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [mul_apply, Fin.sum_univ_two, star_apply, map_ofNat, Complex.ext_iff,
          Complex.mul_re, Complex.mul_im]
    · norm_num [det_fin_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im]⟩

private def eigen (i : Fin 2) : ℂ := ![(3 + 4 * Complex.I) / 5, (3 - 4 * Complex.I) / 5] i
private theorem phase_basis (i : Fin 2) : defining 2 phase (basis i) = eigen i • basis i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [defining, phase, basis, eigen, toLin'_apply, mulVec]

theorem value_vanish (f : Coefficient) (hf : IsInvariant f) (i j k l : Fin 2)
    (h : ¬ Balanced i j k l) : value f i j k l = 0 := by
  have hc := hf phase (basis i) (basis j) (basis k) (basis l)
  simp only [phase_basis, TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    smul_eq_mul] at hc
  have hc' : (eigen i * eigen j * eigen k * eigen l - 1) * value f i j k l = 0 := by
    unfold value
    linear_combination hc
  have hn : eigen i * eigen j * eigen k * eigen l - 1 ≠ 0 := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    all_goals norm_num [Balanced] at h
    all_goals norm_num [eigen, Complex.ext_iff, Complex.mul_re, Complex.mul_im]
  exact (mul_eq_zero.mp hc').resolve_left hn

private theorem flip_basis (i : Fin 2) :
    defining 2 flipTwo (basis i) = if i = 0 then (-1 : ℂ) • basis 1 else basis 0 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [defining, flipTwo, basis, toLin'_apply, mulVec]

theorem complementary (f : Coefficient) (hf : IsInvariant f) :
    value f 1 1 0 0 = value f 0 0 1 1 ∧
    value f 1 0 1 0 = value f 0 1 0 1 ∧
    value f 1 0 0 1 = value f 0 1 1 0 := by
  have h₁ := hf flipTwo (basis 0) (basis 0) (basis 1) (basis 1)
  have h₂ := hf flipTwo (basis 0) (basis 1) (basis 0) (basis 1)
  have h₃ := hf flipTwo (basis 0) (basis 1) (basis 1) (basis 0)
  simp only [flip_basis, show (1 : Fin 2) ≠ 0 by decide, ite_true, ite_false,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul,
    smul_eq_mul, neg_mul, one_mul, neg_neg] at h₁ h₂ h₃
  exact ⟨h₁,h₂,h₃⟩

private def rotation : Group :=
  ⟨!![(3 : ℂ)/5, 4/5; -4/5, 3/5], by
    rw [mem_specialUnitaryGroup_iff]
    constructor
    · rw [mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [mul_apply, Fin.sum_univ_two, star_apply, map_ofNat]
    · norm_num [det_fin_two]⟩

private theorem rotation_basis (i : Fin 2) :
    defining 2 rotation (basis i) = if i = 0 then
      (3/5 : ℂ) • basis 0 - (4/5 : ℂ) • basis 1 else
      (4/5 : ℂ) • basis 0 + (3/5 : ℂ) • basis 1 := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [defining, rotation, basis, toLin'_apply, mulVec, neg_div]

theorem relation (f : Coefficient) (hf : IsInvariant f) :
    value f 0 0 1 1 + value f 0 1 0 1 + value f 0 1 1 0 = 0 := by
  have h := hf rotation (basis 0) (basis 0) (basis 0) (basis 1)
  simp [rotation_basis, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
    TensorProduct.tmul_add, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, map_add, map_sub, map_smul, smul_eq_mul, ← value_eq] at h
  simp [value_vanish f hf, Balanced] at h
  obtain ⟨h₁,h₂,h₃⟩ := complementary f hf
  rw [h₁,h₂,h₃] at h
  linear_combination (625/84 : ℂ) * h

def eps (a b : Space) : ℂ := a 0 * b 1 - a 1 * b 0

theorem value_formula (f : Coefficient) (hf : IsInvariant f) (i j k l : Fin 2) :
    value f i j k l = value f 0 1 0 1 * (eps (basis i) (basis j) * eps (basis k) (basis l)) +
      value f 0 0 1 1 * (eps (basis i) (basis k) * eps (basis j) (basis l)) := by
  obtain ⟨h₁,h₂,h₃⟩ := complementary f hf
  have hr := relation f hf
  by_cases hb : Balanced i j k l
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    all_goals norm_num [Balanced] at hb
    all_goals norm_num [eps, basis, Pi.single_apply, Fin.ext_iff, h₁,h₂,h₃]
    all_goals linear_combination hr
  · rw [value_vanish f hf i j k l hb]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
    all_goals norm_num [Balanced] at hb
    all_goals simp [eps, basis]

def pairing (cross : Bool) : MultilinearMap ℂ (fun _ : Fin 4 => Space) ℂ :=
  MultilinearMap.mk' (fun v => if cross then eps (v 0) (v 2) * eps (v 1) (v 3)
    else eps (v 0) (v 1) * eps (v 2) (v 3))
    (by intro v i x y; cases cross <;> fin_cases i <;>
      simp [eps, Function.update, Fin.ext_iff] <;> ring)
    (by intro v i z x; cases cross <;> fin_cases i <;>
      simp [eps, Function.update, Fin.ext_iff] <;> ring)

def tensorPairing (cross : Bool) : Coefficient := FourTensorMultilinear.lift (pairing cross)

theorem tensorPairing_apply (cross : Bool) (a b c d : Space) :
    tensorPairing cross ((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) =
      if cross then eps a c * eps b d else eps a b * eps c d :=
  FourTensorMultilinear.lift_tprod (pairing cross) ![a,b,c,d]

theorem formula (f : Coefficient) (hf : IsInvariant f) :
    f = value f 0 1 0 1 • tensorPairing false + value f 0 0 1 1 • tensorPairing true := by
  let b := Pi.basisFun ℂ (Fin 2)
  apply ((b.tensorProduct b).tensorProduct (b.tensorProduct b)).ext
  rintro ⟨⟨i,j⟩,⟨k,l⟩⟩
  simpa only [Module.Basis.tensorProduct_apply, b, Pi.basisFun_apply,
    LinearMap.add_apply, LinearMap.smul_apply, tensorPairing_apply,
    Bool.false_eq_true, ite_false, ite_true, smul_eq_mul, basis, value] using
    value_formula f hf i j k l

theorem eps_invariant (g : Group) (a b : Space) :
    eps (defining 2 g a) (defining 2 g b) = eps a b := by
  have hd := (mem_specialUnitaryGroup_iff.mp g.property).2
  calc
    _ = (g.val.det) * eps a b := by
      simp [eps, defining, toLin'_apply, mulVec, det_fin_two]
      ring
    _ = _ := by rw [hd, one_mul]

theorem tensorPairing_invariant (cross : Bool) : IsInvariant (tensorPairing cross) := by
  intro g a b c d
  simp only [tensorPairing_apply, eps_invariant]

def invariantSpace : Submodule ℂ Coefficient where
  carrier := {f | IsInvariant f}
  zero_mem' := by intro g a b c d; rfl
  add_mem' := by intro f h hf hh g a b c d; exact congrArg₂ (· + ·) (hf g a b c d) (hh g a b c d)
  smul_mem' := by intro z f hf g a b c d; exact congrArg (z • ·) (hf g a b c d)

/-- Two probe evaluations, with inverse given by the two epsilon products. -/
def coordinates : invariantSpace ≃ₗ[ℂ] (ℂ × ℂ) where
  toFun f := (value f.val 0 1 0 1, value f.val 0 0 1 1)
  invFun c := ⟨c.1 • tensorPairing false + c.2 • tensorPairing true,
    invariantSpace.add_mem (invariantSpace.smul_mem _ (tensorPairing_invariant false))
      (invariantSpace.smul_mem _ (tensorPairing_invariant true))⟩
  left_inv f := by apply Subtype.ext; exact (formula f.val f.property).symm
  right_inv c := by
    rcases c with ⟨a,b⟩
    simp [value, tensorPairing_apply, eps, basis]
  map_add' f h := rfl
  map_smul' z f := rfl

end
end Math.FourDoubletInvariant
