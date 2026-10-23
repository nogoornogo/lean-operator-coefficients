import Math.Algebra.Jets.MixedFirstJetWords

/-! Curried first-derivative tensors in a possibly noncommutative algebra.
The derivative can mark either odd factor or the first even factor. -/
namespace Math.MixedFirstJetTensor
set_option autoImplicit false
noncomputable section
variable {A U W : Type*} [Ring A] [Algebra ℂ A]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
abbrev Dir := Fin 4 →₀ ℂ
variable (D : Fin 4 → A →ₗ[ℂ] A)

def directional : Dir →ₗ[ℂ] A →ₗ[ℂ] A :=
  ∑ i : Fin 4, (Finsupp.lapply i).smulRight (D i)

theorem directional_apply (u : Dir) (p : A) : directional D u p = ∑ i : Fin 4, u i • D i p := by
  simp [directional]

@[simp] theorem directional_single (i : Fin 4) (c : ℂ) :
    directional D (Finsupp.single i c) = c • D i := by
  simp [directional,Finsupp.single_apply]

theorem directional_covariant (phi : A →ₗ[ℂ] A) (delta : Dir →ₗ[ℂ] Dir)
    (h : ∀ i p, phi (D i p) =
      ∑ j : Fin 4, (delta (Finsupp.single i 1)) j • D j (phi p))
    (u : Dir) (p : A) :
    phi (directional D u p) = directional D (delta u) (phi p) := by
  have hu : u = ∑ i : Fin 4, u i • Finsupp.single i (1 : ℂ) := by
    ext i
    simp
  conv_rhs => rw [hu,map_sum]
  simp only [directional_apply,map_sum,map_smul,h,LinearMap.sum_apply,
    LinearMap.smul_apply,Finset.smul_sum,smul_smul]

variable (L : U →ₗ[ℂ] A) (R : W →ₗ[ℂ] A) (q t : A)

def word (r : Fin 3) (u : Dir) (x : U) (y : W) : A := match r with
  | 0 => directional D u (L x) * R y * q * t
  | 1 => L x * directional D u (R y) * q * t
  | 2 => L x * R y * directional D u q * t

def tensor1 (f : A →ₗ[ℂ] ℂ) (r : Fin 3) (x : U) (y : W) : Dir →ₗ[ℂ] ℂ where
  toFun u := f (word D L R q t r u x y)
  map_add' u v := by
    fin_cases r <;> simp [word,map_add,LinearMap.add_apply,add_mul,mul_add]
  map_smul' c u := by
    fin_cases r <;> simp [word,map_smul,LinearMap.smul_apply]

def tensor2 (f : A →ₗ[ℂ] ℂ) (r : Fin 3) (x : U) : W →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun y := tensor1 D L R q t f r x y
  map_add' x y := by
    ext u
    fin_cases r <;> simp [tensor1,word,map_add,add_mul,mul_add]
  map_smul' c y := by
    ext u
    fin_cases r <;> simp [tensor1,word,map_smul]

def tensor (f : A →ₗ[ℂ] ℂ) (r : Fin 3) : U →ₗ[ℂ] W →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun x := tensor2 D L R q t f r x
  map_add' x y := by
    ext w u
    fin_cases r <;> simp [tensor2,tensor1,word,map_add,add_mul]
  map_smul' c x := by
    ext w u
    fin_cases r <;> simp [tensor2,tensor1,word,map_smul]

theorem tensor_apply (f : A →ₗ[ℂ] ℂ) (r : Fin 3) (x : U) (y : W) (u : Dir) :
    tensor D L R q t f r x y u = f (word D L R q t r u x y) := rfl

theorem transport_word (phi : A →ₐ[ℂ] A) (alpha : U →ₗ[ℂ] U) (beta : W →ₗ[ℂ] W)
    (delta : Dir →ₗ[ℂ] Dir)
    (hL : ∀ x, phi (L x) = L (alpha x)) (hR : ∀ y, phi (R y) = R (beta y))
    (hq : phi q = q) (ht : phi t = t)
    (hD : ∀ u p, phi (directional D u p) = directional D (delta u) (phi p))
    (r : Fin 3) (u : Dir) (x : U) (y : W) :
    phi (word D L R q t r u x y) = word D L R q t r (delta u) (alpha x) (beta y) := by
  fin_cases r <;> simp only [word,map_mul,hD,hL,hR,hq,ht]

end
end Math.MixedFirstJetTensor

namespace Math.MixedFirstJetTensor
set_option autoImplicit false
noncomputable section
open MixedJetAlgebra
variable {F B U W : Type*}
  [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]

theorem mixed_directional_mem (u : Dir) {n m e : ℕ} {p : Algebra F B (Fin 4)}
    (hp : p ∈ grade F B (Fin 4) n m e) :
    directional (totalDerivative (F := F) (B := B)) u p ∈ grade F B (Fin 4) n m (e+1) := by
  rw [directional_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (totalDerivative_mem (F := F) (B := B) (I := Fin 4) i hp))

theorem mixed_product_mem {a b q t : Algebra F B (Fin 4)} {d e j k : ℕ}
    (ha : a ∈ grade F B (Fin 4) 1 0 d) (hb : b ∈ grade F B (Fin 4) 1 0 e)
    (hq : q ∈ grade F B (Fin 4) 0 1 j) (ht : t ∈ grade F B (Fin 4) 0 3 k) :
    a*b*q*t ∈ grade F B (Fin 4) 2 4 (d+e+j+k) :=
  mul_mem (F := F) (B := B) (I := Fin 4)
    (mul_mem (F := F) (B := B) (I := Fin 4)
      (mul_mem (F := F) (B := B) (I := Fin 4) ha hb) hq) ht

theorem mixed_word_mem
    (L : U →ₗ[ℂ] Algebra F B (Fin 4)) (R : W →ₗ[ℂ] Algebra F B (Fin 4))
    (q t : Algebra F B (Fin 4))
    (hL : ∀ x, L x ∈ grade F B (Fin 4) 1 0 0)
    (hR : ∀ y, R y ∈ grade F B (Fin 4) 1 0 0)
    (hq : q ∈ grade F B (Fin 4) 0 1 0) (ht : t ∈ grade F B (Fin 4) 0 3 0)
    (r : Fin 3) (u : Dir) (x : U) (y : W) :
    word (totalDerivative (F := F) (B := B)) L R q t r u x y ∈ grade F B (Fin 4) 2 4 1 := by
  fin_cases r <;> dsimp only [word]
  · exact mixed_product_mem (F := F) (B := B)
      (a := directional (totalDerivative (F := F) (B := B)) u (L x)) (b := R y)
      (q := q) (t := t) (d := 1) (e := 0) (j := 0) (k := 0)
      (mixed_directional_mem (F := F) (B := B) u (hL x)) (hR y) hq ht
  · exact mixed_product_mem (F := F) (B := B)
      (a := L x) (b := directional (totalDerivative (F := F) (B := B)) u (R y))
      (q := q) (t := t) (d := 0) (e := 1) (j := 0) (k := 0)
      (hL x) (mixed_directional_mem (F := F) (B := B) u (hR y)) hq ht
  · exact mixed_product_mem (F := F) (B := B)
      (a := L x) (b := R y) (q := directional (totalDerivative (F := F) (B := B)) u q)
      (t := t) (d := 0) (e := 0) (j := 1) (k := 0)
      (hL x) (hR y) (mixed_directional_mem (F := F) (B := B) u hq) ht

end
end Math.MixedFirstJetTensor
