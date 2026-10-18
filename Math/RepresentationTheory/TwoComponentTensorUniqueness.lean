import Math.RepresentationTheory.TwoComponentSymmetricTensor

/-! Exhaustive triplet contraction from a doublet pair. Only two explicit
group elements are needed, so the argument applies to SL(2,C) and SU(2). -/
namespace Math.TwoComponentTensorUniqueness
set_option autoImplicit false
noncomputable section
open Representation TwoComponentSymmetricTensor Matrix
open scoped TensorProduct

def basis2 (i : Fin 2) : Doublet := Pi.single i 1
def basis3 (i : Fin 3) : Triplet := Pi.single i 1

def Allowed (i j : Fin 2) (k : Fin 3) : Prop :=
  (i = 0 ∧ j = 0 ∧ k = 0) ∨ (i ≠ j ∧ k = 1) ∨ (i = 1 ∧ j = 1 ∧ k = 2)

instance (i j : Fin 2) (k : Fin 3) : Decidable (Allowed i j k) :=
  inferInstanceAs (Decidable ((i = 0 ∧ j = 0 ∧ k = 0) ∨
    (i ≠ j ∧ k = 1) ∨ (i = 1 ∧ j = 1 ∧ k = 2)))

variable {K : Type*} [Group K] (r : K →* Group)

abbrev Coefficient := IntertwiningMap
  (Representation.tprod (doublet.comp r) (doublet.comp r))
  (triplet.comp r)

def restrictedPair : Coefficient r where
  toLinearMap := pair.toLinearMap
  isIntertwining' g := pair.isIntertwining' (r g)

def value (f : Coefficient r) (i j : Fin 2) (k : Fin 3) : ℂ :=
  f (basis2 i ⊗ₜ[ℂ] basis2 j) k

theorem expand (f : Coefficient r) (x y : Doublet) (k : Fin 3) :
    f (x ⊗ₜ[ℂ] y) k = x 0 * y 0 * value r f 0 0 k +
      x 0 * y 1 * value r f 0 1 k + x 1 * y 0 * value r f 1 0 k +
      x 1 * y 1 * value r f 1 1 k := by
  have hx : x = x 0 • basis2 0 + x 1 • basis2 1 := by
    ext i; fin_cases i <;> simp [basis2]
  have hy : y = y 0 • basis2 0 + y 1 • basis2 1 := by
    ext i; fin_cases i <;> simp [basis2]
  conv_lhs => rw [hx, hy]
  simp [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.smul_tmul,
    TensorProduct.tmul_smul, value, mul_comm, mul_left_comm, mul_assoc]
  ring

theorem vanish (f : Coefficient r) (g : K) (u v : ℂ)
    (hg : (r g : Matrix (Fin 2) (Fin 2) ℂ) = !![u, 0; 0, v])
    (hn : ∀ i j k, ¬ Allowed i j k →
      ![u, v] i * ![u, v] j - ![u^2, u*v, v^2] k ≠ 0)
    (i j : Fin 2) (k : Fin 3) (h : ¬ Allowed i j k) : value r f i j k = 0 := by
  have hd (i : Fin 2) : (doublet.comp r) g (basis2 i) = ![u,v] i • basis2 i := by
    ext l
    fin_cases i <;> fin_cases l <;> simp [doublet, hg, basis2, Matrix.mulVec]
  have hc := congrFun (IntertwiningMap.isIntertwining _ _ f g
    (basis2 i ⊗ₜ[ℂ] basis2 j)) k
  simp only [Representation.tprod_apply, TensorProduct.map_tmul, hd,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, map_smul] at hc
  have ht (z : Triplet) : (triplet.comp r) g z k = ![u^2,u*v,v^2] k * z k := by
    fin_cases k <;> simp [triplet, hg, squareMatrix, Matrix.mulVec,
      Matrix.vecHead, Matrix.vecTail]
  rw [ht] at hc
  change (![u,v] j * (![u,v] i * value r f i j k)) =
    ![u^2,u*v,v^2] k * value r f i j k at hc
  have he : (![u,v] i * ![u,v] j - ![u^2,u*v,v^2] k) * value r f i j k = 0 := by
    linear_combination hc
  exact (mul_eq_zero.mp he).resolve_left (hn i j k h)

/-- Exhaustiveness follows from a diagonal element and a nondegenerate mixer. -/
theorem unique (g m : K) (u v a b c d : ℂ)
    (hg : (r g : Matrix (Fin 2) (Fin 2) ℂ) = !![u,0;0,v])
    (hn : ∀ i j k, ¬ Allowed i j k →
      ![u,v] i * ![u,v] j - ![u^2,u*v,v^2] k ≠ 0)
    (hm : (r m : Matrix (Fin 2) (Fin 2) ℂ) = !![a,b;c,d])
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (f : Coefficient r) :
    f = value r f 0 0 0 • restrictedPair r := by
  have hz (i j : Fin 2) (k : Fin 3) (h : ¬ Allowed i j k) := vanish r f g u v hg hn i j k h
  have hcov (i j : Fin 2) (k : Fin 3) := congrFun
    (IntertwiningMap.isIntertwining _ _ f m (basis2 i ⊗ₜ[ℂ] basis2 j)) k
  have he2 := hcov 0 0 2
  have he0 := hcov 0 1 0
  have he1 := hcov 0 0 1
  simp only [Representation.tprod_apply, TensorProduct.map_tmul] at he2 he0 he1
  rw [expand] at he2 he0 he1
  simp [doublet, triplet, hm, squareMatrix, basis2, Matrix.mulVec,
    Matrix.vecHead, Matrix.vecTail] at he2 he0 he1
  change a*a*value r f 0 0 2 + a*c*value r f 0 1 2 +
    c*a*value r f 1 0 2 + c*c*value r f 1 1 2 =
    c^2*value r f 0 0 0 + (2*c*d*value r f 0 0 1 + d^2*value r f 0 0 2) at he2
  change a*b*value r f 0 0 0 + a*d*value r f 0 1 0 +
    c*b*value r f 1 0 0 + c*d*value r f 1 1 0 =
    a^2*value r f 0 1 0 + (2*a*b*value r f 0 1 1 + b^2*value r f 0 1 2) at he0
  change a*a*value r f 0 0 1 + a*c*value r f 0 1 1 +
    c*a*value r f 1 0 1 + c*c*value r f 1 1 1 =
    a*c*value r f 0 0 0 + ((a*d+b*c)*value r f 0 0 1 + b*d*value r f 0 0 2) at he1
  simp only [
    show value r f 0 0 2 = 0 from hz 0 0 2 (by decide),
    show value r f 0 1 2 = 0 from hz 0 1 2 (by decide),
    show value r f 1 0 2 = 0 from hz 1 0 2 (by decide),
    show value r f 0 1 0 = 0 from hz 0 1 0 (by decide),
    show value r f 1 0 0 = 0 from hz 1 0 0 (by decide),
    show value r f 1 1 0 = 0 from hz 1 1 0 (by decide),
    show value r f 0 0 1 = 0 from hz 0 0 1 (by decide),
    show value r f 1 1 1 = 0 from hz 1 1 1 (by decide),
    mul_zero, zero_add, add_zero] at he2 he0 he1
  have h2 : value r f 1 1 2 = value r f 0 0 0 := by
    apply mul_left_cancel₀ (mul_ne_zero hc hc)
    linear_combination he2
  have h0 : value r f 0 1 1 = value r f 0 0 0 / 2 := by
    apply mul_left_cancel₀ (mul_ne_zero ha hb)
    linear_combination -(1/2 : ℂ) * he0
  have h1 : value r f 1 0 1 = value r f 0 0 0 / 2 := by
    apply mul_left_cancel₀ (mul_ne_zero ha hc)
    linear_combination he1 - a*c*h0
  apply IntertwiningMap.ext
  apply ((Pi.basisFun ℂ (Fin 2)).tensorProduct (Pi.basisFun ℂ (Fin 2))).ext
  rintro ⟨i,j⟩
  ext k
  simp only [Module.Basis.tensorProduct_apply, Pi.basisFun_apply]
  change value r f i j k = value r f 0 0 0 * (pair (basis2 i ⊗ₜ[ℂ] basis2 j)) k
  by_cases h : Allowed i j k
  · fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num [Allowed, Fin.ext_iff] at h
    all_goals simp [pair_tmul, basis2, h0, h1, h2]
    all_goals ring
  · rw [hz i j k h]
    fin_cases i <;> fin_cases j <;> fin_cases k
    all_goals norm_num [Allowed, Fin.ext_iff] at h
    all_goals simp [pair_tmul, basis2]

end
end Math.TwoComponentTensorUniqueness
