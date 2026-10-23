import Physics.FieldTheory.Jets.LorentzRankFour.Core.Contractions

/-! The inverse Minkowski pairing on actual derivative directions. -/
namespace Physics.LorentzRankFour
set_option autoImplicit false
noncomputable section
open Math LorentzDirections LorentzFiniteControls Matrix

def pairing (x y : Coordinates) : ℂ := x 0*y 0-x 1*y 1-x 2*y 2-x 3*y 3

theorem pairing_invariant (g : Group) (x y : Coordinates) :
    pairing (vector g x) (vector g y) = pairing x y := by
  have hxy := quadratic_invariant g (x+y)
  have hx := quadratic_invariant g x
  have hy := quadratic_invariant g y
  simp only [map_add,quadratic,Pi.add_apply] at hxy
  dsimp only [quadratic] at hx hy
  dsimp only [pairing]
  linear_combination (1/2 : ℂ)*hxy-(1/2 : ℂ)*hx-(1/2 : ℂ)*hy

abbrev matrix (g : Group) := LinearMap.toMatrix' (vector g)
abbrev J : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal eta

theorem J_square : J*J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J,eta,Matrix.mul_apply,Fin.sum_univ_succ]

theorem matrix_inverse (g : Group) : matrix g*matrix g⁻¹ = 1 := by
  rw [← LinearMap.toMatrix'_mul,← map_mul,mul_inv_cancel,map_one,LinearMap.toMatrix'_one]

theorem matrix_column (g : Group) : (matrix g)ᵀ*J*matrix g = J := by
  ext i j
  have he := pairing_invariant g (Pi.single i 1) (Pi.single j 1)
  fin_cases i <;> fin_cases j
  all_goals simp [pairing,Matrix.mul_apply,Matrix.transpose_apply,LinearMap.toMatrix'_apply,
    J,eta,Fin.sum_univ_succ] at he ⊢
  all_goals linear_combination he

theorem matrix_row (g : Group) : matrix g*J*(matrix g)ᵀ = J := by
  have ht : (matrix g)ᵀ = J*matrix g⁻¹*J := by
    calc
      _ = ((matrix g)ᵀ*J*matrix g)*matrix g⁻¹*J := by
        simp only [Matrix.mul_assoc,matrix_inverse,J_square,Matrix.mul_one]
      _ = _ := by rw [matrix_column]
  rw [ht]
  calc
    _ = matrix g*(J*J)*matrix g⁻¹*J := by simp only [Matrix.mul_assoc]
    _ = J := by rw [J_square,Matrix.mul_one,matrix_inverse,Matrix.one_mul]

def metricPair : Dir →ₗ[ℂ] Dir →ₗ[ℂ] ℂ where
  toFun u := {
    toFun v := ∑ i : Fin 4, eta i*u i*v i
    map_add' v w := by simp [Finsupp.add_apply,mul_add,Finset.sum_add_distrib]
    map_smul' c v := by
      change (∑ i : Fin 4, eta i*u i*(c*v i)) = c*(∑ i : Fin 4, eta i*u i*v i)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring }
  map_add' u v := by
    apply LinearMap.ext; intro w
    simp [Finsupp.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
  map_smul' c u := by
    apply LinearMap.ext; intro v
    change (∑ i : Fin 4, eta i*(c*u i)*v i) = c*(∑ i : Fin 4, eta i*u i*v i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem metricPair_apply (u v : Dir) : metricPair u v = ∑ i : Fin 4, eta i*u i*v i := rfl

theorem metricPair_basis (i j : Fin 4) : metricPair (E i) (E j) = metric i j := by
  by_cases hij : i = j
  · subst j
    simp [metricPair_apply,E,Finsupp.single_apply,metric,eta]
  · simp [metricPair_apply,E,Finsupp.single_apply,metric,eta,hij]

theorem matrix_row_entry (g : Group) (i j : Fin 4) :
    (∑ k : Fin 4, eta k*matrix g i k*matrix g j k) = metric i j := by
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M i j) (matrix_row g)
  change ((matrix g*Matrix.diagonal eta)*(matrix g)ᵀ) i j = (Matrix.diagonal eta) i j at he
  rw [Matrix.mul_apply] at he
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply] at he
  by_cases hij : i = j
  · subst j
    simpa [metric,eta,mul_comm,mul_left_comm,mul_assoc] using he
  · simpa [Matrix.diagonal_apply_ne _ hij,metric,hij,eta,mul_comm,mul_left_comm,mul_assoc] using he

theorem metricPair_invariant_basis (g : Group) (i j : Fin 4) :
    metricPair (direction g (E i)) (direction g (E j)) = metricPair (E i) (E j) := by
  have he := matrix_row_entry g⁻¹ i j
  rw [metricPair_apply,metricPair_basis]
  simp only [E,direction_single]
  simpa only [matrix,LinearMap.toMatrix'_apply] using he

theorem metricPair_invariant (g : Group) (u v : Dir) :
    metricPair (direction g u) (direction g v) = metricPair u v := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add,LinearMap.add_apply,hu,hw]
  | single i c =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw]
    | single j d =>
      have hi : Finsupp.single i c = c • E i := by simp [E]
      have hj : Finsupp.single j d = d • E j := by simp [E]
      simp only [hi,hj,map_smul,LinearMap.smul_apply,metricPair_invariant_basis]

theorem reconstruct (T : Tensor) (a c : ℂ)
    (hc : ∀ i j k l : Fin 4, T (E i) (E j) (E k) (E l) =
      a*metric i j*metric k l+c*(metric i k*metric j l+metric i l*metric j k))
    (u v w x : Dir) : T u v w x = a*metricPair u v*metricPair w x+
      c*(metricPair u w*metricPair v x+metricPair u x*metricPair v w) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u y hu hy =>
    simp only [map_add,LinearMap.add_apply,hu,hy]
    ring
  | single i z =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v y hv hy =>
      simp only [map_add,LinearMap.add_apply,hv,hy]
      ring
    | single j t =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w y hw hy =>
        simp only [map_add,LinearMap.add_apply,hw,hy]
        ring
      | single k s =>
        induction x using Finsupp.induction_linear with
        | zero => simp
        | add x y hx hy =>
          simp only [map_add,hx,hy]
          ring
        | single l q =>
          have hi : Finsupp.single i z = z • E i := by simp [E]
          have hj : Finsupp.single j t = t • E j := by simp [E]
          have hk : Finsupp.single k s = s • E k := by simp [E]
          have hl : Finsupp.single l q = q • E l := by simp [E]
          simp only [hi,hj,hk,hl,map_smul,LinearMap.smul_apply,smul_eq_mul,metricPair_basis,hc]
          ring

theorem invariant_of_components (T : Tensor) (a c : ℂ)
    (hc : ∀ i j k l : Fin 4, T (E i) (E j) (E k) (E l) =
      a*metric i j*metric k l+c*(metric i k*metric j l+metric i l*metric j k))
    (g : Group) (u v w x : Dir) :
    T (direction g u) (direction g v) (direction g w) (direction g x) = T u v w x := by
  rw [reconstruct T a c hc,reconstruct T a c hc]
  simp only [metricPair_invariant]

end
end Physics.LorentzRankFour
