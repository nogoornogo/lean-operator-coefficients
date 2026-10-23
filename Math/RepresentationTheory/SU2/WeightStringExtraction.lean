import Math.RepresentationTheory.Weights.SparseWeightPolynomial

/-! Coefficient convolution and cancellation of a finite weight string. -/
namespace Math.WeightStringExtraction
set_option autoImplicit false
open ComputableWeightPolynomial
open scoped BigOperators

theorem coefficient_append {W : Type*} [DecidableEq W] (p q : Terms W) (w : W) :
    coefficient (p ++ q) w = coefficient p w + coefficient q w := by
  simp [coefficient]

theorem coefficient_scaledShift {W : Type*} [AddCommGroup W] [DecidableEq W]
    (p : Terms W) (a w : W) (c : ℤ) :
    coefficient (p.map (fun x => (a+x.1,c*x.2))) w = c * coefficient p (w-a) := by
  induction p with
  | nil => simp [coefficient]
  | cons x p ih =>
    have he : a+x.1=w ↔ x.1=w-a := by
      rw [eq_sub_iff_add_eq]
      simp only [add_comm]
    simpa [coefficient,he,mul_add,mul_ite] using ih

theorem coefficient_multiply {W : Type*} [AddCommGroup W] [DecidableEq W]
    (p q : Terms W) (w : W) :
    coefficient (multiply p q) w =
      (q.map (fun y => y.2 * coefficient p (w-y.1))).sum := by
  induction p with
  | nil => simp [multiply,coefficient]
  | cons x p ih =>
    change coefficient ((q.map (fun y => (x.1+y.1,x.2*y.2))) ++ multiply p q) w = _
    rw [coefficient_append,coefficient_scaledShift,ih]
    simp only [coefficient,List.map_cons,List.sum_cons,mul_add,List.sum_map_add,
      ← List.sum_map_mul_left]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro y _
    have he : y.1=w-x.1 ↔ x.1=w-y.1 := by
      rw [eq_sub_iff_add_eq,eq_sub_iff_add_eq]
      simp only [add_comm]
    simp [he,mul_ite,mul_comm]

theorem telescope {R : Type*} [AddCommGroup R] (f : ℕ → R) (m : ℕ) :
    (∑ j ∈ Finset.range (m+1), f j) -
      (∑ j ∈ Finset.range (m+1), f (j+1)) = f 0 - f (m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ (n := m+1),Finset.sum_range_succ (n := m+1)]
    calc
      _ = ((∑ j ∈ Finset.range (m+1), f j) -
          (∑ j ∈ Finset.range (m+1), f (j+1))) + f (m+1) - f (m+1+1) := by abel
      _ = _ := by rw [ih]; abel

def string {W R : Type*} [AddCommGroup W] [AddCommGroup R]
    (f : W → R) (a root : W) (m : ℕ) (w : W) : R :=
  ∑ j ∈ Finset.range (m+1), f (w+a+j • root)

theorem difference_string {W R : Type*} [AddCommGroup W] [AddCommGroup R]
    (f : W → R) (a root : W) (m : ℕ) (w : W) :
    CompactWeylExtraction.difference root (string f a root m) w =
      f (w+a) - f (w+a+(m+1) • root) := by
  have h (j : ℕ) : w+root+a+j • root = w+a+(j+1) • root := by
    rw [add_nsmul,one_nsmul]
    abel
  simp only [CompactWeylExtraction.difference,string,h]
  simpa using telescope (fun j => f (w+a+j • root)) m

theorem extractAt_append {W R : Type*} [AddCommGroup W] [AddCommGroup R]
    (rs ss : List W) (f : W → R) (w : W) :
    CompactWeylExtraction.extractAt (rs ++ ss) f w =
      CompactWeylExtraction.extractAt rs (CompactWeylExtraction.extractAt ss f) w := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih => simp only [List.cons_append,CompactWeylExtraction.extractAt,
      CompactWeylExtraction.difference,ih]

theorem extractAt_difference {W R : Type*} [AddCommGroup W] [AddCommGroup R]
    (rs : List W) (root : W) (f : W → R) (w : W) :
    CompactWeylExtraction.extractAt rs (CompactWeylExtraction.difference root f) w =
      CompactWeylExtraction.difference root (CompactWeylExtraction.extractAt rs f) w := by
  induction rs generalizing w with
  | nil => rfl
  | cons r rs ih =>
    simp only [CompactWeylExtraction.extractAt,CompactWeylExtraction.difference,ih]
    have he : w+r+root = w+root+r := by abel
    simp only [he]
    abel

theorem constantTerm_string {W R : Type*} [AddCommGroup W] [AddCommGroup R]
    (rs ss : List W) (f : W → R) (a root : W) (m : ℕ) :
    CompactWeylExtraction.constantTerm (rs ++ root :: ss) (string f a root m) =
      CompactWeylExtraction.constantTerm (rs ++ ss)
        (fun w => f (w+a) - f (w+a+(m+1) • root)) := by
  have he : CompactWeylExtraction.difference root
      (CompactWeylExtraction.extractAt ss (string f a root m)) =
      CompactWeylExtraction.extractAt ss
        (fun w => f (w+a) - f (w+a+(m+1) • root)) := by
    funext w
    rw [← extractAt_difference]
    congr 1
    funext v
    exact difference_string f a root m v
  simp only [CompactWeylExtraction.constantTerm,extractAt_append]
  change CompactWeylExtraction.extractAt rs
    (CompactWeylExtraction.difference root
      (CompactWeylExtraction.extractAt ss (string f a root m))) 0 = _
  rw [he]

end Math.WeightStringExtraction
