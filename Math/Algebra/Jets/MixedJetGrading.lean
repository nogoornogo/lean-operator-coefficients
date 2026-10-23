import Math.Algebra.Jets.MixedJetAlgebra
import Mathlib.LinearAlgebra.Multilinear.Basis

/-! Joint field/statistics/derivative subspaces spanned inside the actual
mixed jet algebra. Derivative distributions are retained until IBP descent. -/
namespace Math.MixedJetAlgebra
set_option autoImplicit false
noncomputable section
open JetLinear ScalarJetAlgebra
open scoped TensorProduct

variable {F B I : Type*} {n m : ℕ}

def word (f : Fin n → Index F I) (b : Fin m → Index B I) : Algebra F B I :=
  ExteriorAlgebra.ιMulti ℂ n (fun i => Finsupp.single (f i) 1) ⊗ₜ[ℂ]
    ∏ j, MvPolynomial.X (b j)

def wordOrder (f : Fin n → Index F I) (b : Fin m → Index B I) : ℕ :=
  (∑ i, order (f i).2) + ∑ j, order (b j).2

def generators (F B I : Type*) (n m d : ℕ) : Set (Algebra F B I) :=
  {p | ∃ (f : Fin n → Index F I) (b : Fin m → Index B I), wordOrder f b = d ∧ word f b = p}

def grade (F B I : Type*) (n m d : ℕ) : Submodule ℂ (Algebra F B I) :=
  Submodule.span ℂ (generators F B I n m d)

theorem word_mem (f : Fin n → Index F I) (b : Fin m → Index B I) :
    word f b ∈ grade F B I n m (wordOrder f b) :=
  Submodule.subset_span ⟨f, b, rfl, rfl⟩

theorem word_mul {p q : ℕ} (f : Fin n → Index F I) (b : Fin m → Index B I)
    (g : Fin p → Index F I) (c : Fin q → Index B I) :
    word f b * word g c = word (Fin.append f g) (Fin.append b c) := by
  simp only [word, Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  · congr 1
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp
  · simp [Fin.prod_univ_add]

theorem wordOrder_append {p q : ℕ} (f : Fin n → Index F I) (b : Fin m → Index B I)
    (g : Fin p → Index F I) (c : Fin q → Index B I) :
    wordOrder (Fin.append f g) (Fin.append b c) = wordOrder f b + wordOrder g c := by
  simp [wordOrder, Fin.sum_univ_add, add_assoc, add_left_comm]

theorem mul_mem {n m d p q e : ℕ} {x y : Algebra F B I}
    (hx : x ∈ grade F B I n m d) (hy : y ∈ grade F B I p q e) :
    x * y ∈ grade F B I (n + p) (m + q) (d + e) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, b, hf, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, c, hg, rfl⟩ := hy
      rw [word_mul]
      have h := word_mem (Fin.append f g) (Fin.append b c)
      rwa [wordOrder_append, hf, hg] at h
    | zero => simp
    | add x y _ _ hx hy => simpa only [mul_add] using (grade F B I _ _ _).add_mem hx hy
    | smul a x _ hx => simpa only [mul_smul_comm] using (grade F B I _ _ _).smul_mem a hx
  | zero => simp
  | add x y _ _ hx hy => simpa only [add_mul] using (grade F B I _ _ _).add_mem hx hy
  | smul a x _ hx => simpa only [smul_mul_assoc] using (grade F B I _ _ _).smul_mem a hx

@[simp] theorem word_empty : word (F := F) (B := B) (I := I) (Fin.elim0) (Fin.elim0) = 1 := by
  simp [word, ExteriorAlgebra.ιMulti_zero_apply, Algebra.TensorProduct.one_def]

theorem word_cons_odd (f : Fin (n + 1) → Index F I) (b : Fin m → Index B I) :
    word f b = odd (f 0) * word (Fin.tail f) b := by
  simp [word, odd, ExteriorAlgebra.ιMulti_succ_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

theorem word_cons_even (b : Fin (m + 1) → Index B I) :
    word (F := F) Fin.elim0 b = even (b 0) * word Fin.elim0 (Fin.tail b) := by
  simp [word, even, ExteriorAlgebra.ιMulti_zero_apply, Fin.prod_univ_succ,
    Algebra.TensorProduct.tmul_mul_tmul]
  rfl

theorem wordOrder_cons_odd (f : Fin (n + 1) → Index F I) (b : Fin m → Index B I) :
    wordOrder f b = order (f 0).2 + wordOrder (Fin.tail f) b := by
  simp [wordOrder, Fin.sum_univ_succ, Fin.tail, Nat.add_assoc]

theorem wordOrder_cons_even (b : Fin (m + 1) → Index B I) :
    wordOrder (F := F) Fin.elim0 b = order (b 0).2 + wordOrder (F := F) Fin.elim0 (Fin.tail b) := by
  simp [wordOrder, Fin.sum_univ_succ, Fin.tail]

theorem odd_mem (j : Index F I) : odd (B := B) j ∈ grade F B I 1 0 (order j.2) := by
  simpa [word, wordOrder, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, odd] using
    word_mem (fun _ : Fin 1 => j) (Fin.elim0 : Fin 0 → Index B I)

theorem even_mem (j : Index B I) : even (F := F) j ∈ grade F B I 0 1 (order j.2) := by
  simpa [word, wordOrder, ExteriorAlgebra.ιMulti_zero_apply, even] using
    word_mem (Fin.elim0 : Fin 0 → Index F I) (fun _ : Fin 1 => j)

theorem order_shift (i : I) (j : Index F I) :
    order (ScalarJetAlgebra.shift i j).2 = order j.2 + 1 := by
  simp [ScalarJetAlgebra.shift, order, map_add, Finsupp.weight_single]

theorem derivative_word_mem (i : I) (f : Fin n → Index F I) (b : Fin m → Index B I) :
    totalDerivative i (word f b) ∈ grade F B I n m (wordOrder f b + 1) := by
  induction n with
  | zero =>
    induction m with
    | zero =>
      have hf : f = Fin.elim0 := Subsingleton.elim _ _
      have hb : b = Fin.elim0 := Subsingleton.elim _ _
      subst hf; subst hb
      rw [word_empty, totalDerivative_one]
      exact (grade F B I _ _ _).zero_mem
    | succ m ih =>
      have hf : f = Fin.elim0 := Subsingleton.elim _ _
      subst hf
      rw [word_cons_even, totalDerivative_mul, totalDerivative_even]
      have h₁ := mul_mem (even_mem (F := F) (ScalarJetAlgebra.shift i (b 0)))
        (word_mem (Fin.elim0 : Fin 0 → Index F I) (Fin.tail b))
      have h₂ := mul_mem (even_mem (F := F) (b 0)) (ih (Fin.tail b))
      have he₁ : order (ScalarJetAlgebra.shift i (b 0)).2 +
          wordOrder (F := F) Fin.elim0 (Fin.tail b) = wordOrder (F := F) Fin.elim0 b + 1 := by
        rw [order_shift, wordOrder_cons_even]; omega
      have he₂ : order (b 0).2 + (wordOrder (F := F) Fin.elim0 (Fin.tail b) + 1) =
          wordOrder (F := F) Fin.elim0 b + 1 := by
        rw [wordOrder_cons_even]; omega
      rw [he₁] at h₁
      rw [he₂] at h₂
      exact (grade F B I _ _ _).add_mem
        (by simpa only [Nat.zero_add, Nat.one_add] using h₁)
        (by simpa only [Nat.zero_add, Nat.one_add] using h₂)
  | succ n ih =>
    rw [word_cons_odd, totalDerivative_mul, totalDerivative_odd]
    have h₁ := mul_mem (odd_mem (B := B) (ScalarJetAlgebra.shift i (f 0))) (word_mem (Fin.tail f) b)
    have h₂ := mul_mem (odd_mem (B := B) (f 0)) (ih (Fin.tail f))
    have he₁ : order (ScalarJetAlgebra.shift i (f 0)).2 + wordOrder (Fin.tail f) b =
        wordOrder f b + 1 := by rw [order_shift, wordOrder_cons_odd]; omega
    have he₂ : order (f 0).2 + (wordOrder (Fin.tail f) b + 1) = wordOrder f b + 1 := by
      rw [wordOrder_cons_odd]; omega
    rw [he₁] at h₁
    rw [he₂] at h₂
    apply (grade F B I (n + 1) m (wordOrder f b + 1)).add_mem
    · simpa only [Nat.zero_add, Nat.one_add] using h₁
    · simpa only [Nat.zero_add, Nat.one_add] using h₂

theorem totalDerivative_mem (i : I) {n m d : ℕ} {p : Algebra F B I}
    (hp : p ∈ grade F B I n m d) : totalDerivative i p ∈ grade F B I n m (d + 1) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, b, hf, rfl⟩ := hx
    simpa only [hf] using derivative_word_mem i f b
  | zero => simpa only [map_zero] using (grade F B I n m (d + 1)).zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using (grade F B I n m (d + 1)).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (grade F B I n m (d + 1)).smul_mem a hx

def derivative (i : I) (n m d : ℕ) : grade F B I n m d →ₗ[ℂ] grade F B I n m (d + 1) where
  toFun p := ⟨totalDerivative i p.val, totalDerivative_mem i p.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

end
end Math.MixedJetAlgebra
