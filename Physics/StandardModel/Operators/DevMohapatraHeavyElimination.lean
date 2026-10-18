import Physics.StandardModel.Operators.DevMohapatraHermitian
import Math.LinearAlgebra.ExteriorNilpotentKernel
import Math.LinearAlgebra.ExteriorOdd

/-! Exact finite inverse for all four heavy components. No external-degree
truncation. The concrete stationary-action bridge is separate. -/
namespace GUT.DevMohapatraHeavyElimination
set_option autoImplicit false
noncomputable section
open scoped Matrix
open DevMohapatraTreeLevel
abbrev V := Fin 36 → ℂ
abbrev R := ExteriorAlgebra ℂ V

def coord (i : Fin 36) : V := Pi.basisFun ℂ (Fin 36) i

def u (c : Fin 3) (r : Fin 2) : V := coord ⟨2*c.val+r.val, by omega⟩
def d (c : Fin 3) (r : Fin 2) : V := coord ⟨6+2*c.val+r.val, by omega⟩
def s (c : Fin 3) (r : Fin 2) : V := coord ⟨12+2*c.val+r.val, by omega⟩
def ub (c : Fin 3) (r : Fin 2) : V := coord ⟨18+2*c.val+r.val, by omega⟩
def db (c : Fin 3) (r : Fin 2) : V := coord ⟨24+2*c.val+r.val, by omega⟩
def sb (c : Fin 3) (r : Fin 2) : V := coord ⟨30+2*c.val+r.val, by omega⟩

def cross (r t : Fin 2) : R :=
  ∑ c, ExteriorAlgebra.ι ℂ (u c r)*ExteriorAlgebra.ι ℂ (ub c t)

theorem cross_degree (r t : Fin 2) :
    cross r t ∈ (Math.ExteriorNilpotentKernel.P (k := ℂ) (V := V))^2 := by
  apply Submodule.sum_mem
  intro c _
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)

def kernel (m M a : ℂ) : Matrix (Fin 4) (Fin 4) R :=
  let c := a*star a/m
  !![0, 0, -(c/M) • cross 0 1, (c/M) • cross 0 0;
     0, 0, -(c/M) • cross 1 1, (c/M) • cross 1 0;
     -(c/star M) • cross 1 0, (c/star M) • cross 0 0, 0, 0;
     -(c/star M) • cross 1 1, (c/star M) • cross 0 1, 0, 0]

theorem kernel_degree (m M a : ℂ) (i j : Fin 4) :
    kernel m M a i j ∈ (Math.ExteriorNilpotentKernel.P (k := ℂ) (V := V))^2 := by
  fin_cases i <;> fin_cases j <;> simp only [kernel]
    <;> first | exact Submodule.zero_mem _ |
      exact Submodule.smul_mem _ _ (cross_degree _ _)

theorem kernel_nilpotent (m M a : ℂ) : (kernel m M a)^19 = 0 := by
  apply Math.ExteriorNilpotentKernel.nilpotent coord
    (Pi.basisFun ℂ (Fin 36)).span_eq (kernel m M a) 2 19
    (kernel_degree m M a)
  norm_num

def source (m M a b : ℂ) : Fin 4 → R :=
  ![-(a*b/m/M) • current u d s 0, -(a*b/m/M) • current u d s 1,
    (star a*star b/m/star M) • current ub db sb 0,
    (star a*star b/m/star M) • current ub db sb 1]

def solution (m M a b : ℂ) : Fin 4 → R :=
  Math.ExteriorNilpotentKernel.solution (kernel m M a) 19 (source m M a b)

/-- The complete coupled system; no truncated correction is supplied. -/
theorem source_equation (m M a b : ℂ) :
    solution m M a b - kernel m M a *ᵥ solution m M a b = source m M a b :=
  Math.ExteriorNilpotentKernel.source_equation _ _ (kernel_nilpotent m M a) _

theorem source_unique (m M a b : ℂ) (n : Fin 4 → R)
    (hn : n-kernel m M a *ᵥ n = source m M a b) : n = solution m M a b :=
  Math.ExteriorNilpotentKernel.unique _ _ (kernel_nilpotent m M a) _ _ hn

theorem cross_commutes (r t : Fin 2) (z : R) : cross r t*z = z*cross r t := by
  have hp (x y : V) (z : R) :
      (ExteriorAlgebra.ι ℂ x*ExteriorAlgebra.ι ℂ y)*z =
        z*(ExteriorAlgebra.ι ℂ x*ExteriorAlgebra.ι ℂ y) := by
    induction z using ExteriorAlgebra.induction with
    | algebraMap a => exact (Algebra.commutes a _).symm
    | ι v => exact even_product_commutes x y v
    | mul z w hz hw => calc
        _ = ((ExteriorAlgebra.ι ℂ x*ExteriorAlgebra.ι ℂ y)*z)*w := (mul_assoc _ _ _).symm
        _ = (z*(ExteriorAlgebra.ι ℂ x*ExteriorAlgebra.ι ℂ y))*w := by rw [hz]
        _ = z*((ExteriorAlgebra.ι ℂ x*ExteriorAlgebra.ι ℂ y)*w) := mul_assoc _ _ _
        _ = _ := by rw [hw, mul_assoc]
    | add z w hz hw => simp only [mul_add, add_mul, hz, hw]
  simp only [cross, Finset.sum_mul, Finset.mul_sum, hp]

/-- Direct left derivatives of the normal-ordered heavy quadratic action.
The barred mass has the sign fixed by literal H.c. -/
def residual (m M a b : ℂ) (n : Fin 4 → R) : Fin 4 → R :=
  let g := a*b/m
  let gb := star a*star b/m
  let c := a*star a/m
  ![-M • n 1 - g • current u d s 1 +
      c • (-n 2*cross 1 1+n 3*cross 1 0),
    M • n 0 + g • current u d s 0 +
      c • (n 2*cross 0 1-n 3*cross 0 0),
    star M • n 3 - gb • current ub db sb 1 +
      c • (n 0*cross 1 1-n 1*cross 0 1),
    -star M • n 2 + gb • current ub db sb 0 +
      c • (-n 0*cross 1 0+n 1*cross 0 0)]

theorem residual_factor (m M a b : ℂ) (hM : M ≠ 0) (n : Fin 4 → R) :
    residual m M a b n =
      let e := n-kernel m M a *ᵥ n-source m M a b
      ![-M • e 1, M • e 0, star M • e 3, -star M • e 2] := by
  have hcM : star M ≠ 0 := star_ne_zero.mpr hM
  ext i
  fin_cases i <;>
    simp [residual, kernel, source, Pi.sub_apply, Matrix.vecHead, Matrix.vecTail, dotProduct, Fin.sum_univ_succ,
      smul_smul, cross_commutes] <;>
    match_scalars <;> field_simp [hM, hcM]

theorem stationary (m M a b : ℂ) (hM : M ≠ 0) :
    residual m M a b (solution m M a b) = 0 := by
  rw [residual_factor m M a b hM]
  have h := source_equation m M a b
  have hz : solution m M a b - kernel m M a *ᵥ solution m M a b - source m M a b = 0 := by
    rw [h, sub_self]
  rw [hz]
  simp

theorem stationary_unique (m M a b : ℂ) (hM : M ≠ 0) (n : Fin 4 → R)
    (hn : residual m M a b n = 0) : n = solution m M a b := by
  apply source_unique
  have hcM : star M ≠ 0 := star_ne_zero.mpr hM
  rw [residual_factor m M a b hM] at hn
  have h0 := congrFun hn 0
  have h1 := congrFun hn 1
  have h2 := congrFun hn 2
  have h3 := congrFun hn 3
  ext i
  fin_cases i <;> simp_all [sub_eq_zero]

theorem cross_even (r t : Fin 2) : CliffordAlgebra.involute (cross r t) = cross r t := by
  simp [cross, map_sum, map_mul, CliffordAlgebra.involute_ι]

theorem kernel_even (m M a : ℂ) (i j : Fin 4) :
    CliffordAlgebra.involute (kernel m M a i j) = kernel m M a i j := by
  fin_cases i <;> fin_cases j <;> simp [kernel, cross_even]

theorem current_odd (x y z : Fin 3 → Fin 2 → V) (r : Fin 2) :
    Math.ExteriorOdd.Odd (current x y z r) := by
  simp [Math.ExteriorOdd.Odd, current, term, cubic_apply,
    map_sum, map_mul, CliffordAlgebra.involute_ι, Finset.sum_neg_distrib]

theorem source_odd (m M a b : ℂ) (i : Fin 4) :
    Math.ExteriorOdd.Odd (source m M a b i) := by
  fin_cases i <;> simp [Math.ExteriorOdd.Odd, source,
    show ∀ x y z r, CliffordAlgebra.involute (current x y z r) = -current x y z r
      from current_odd]

theorem kernel_preserves_odd (m M a : ℂ) (n : Fin 4 → R)
    (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) (i : Fin 4) :
    Math.ExteriorOdd.Odd ((kernel m M a *ᵥ n) i) := by
  simp only [Math.ExteriorOdd.Odd] at hn
  simp only [Math.ExteriorOdd.Odd, Matrix.mulVec, dotProduct, map_sum, map_mul,
    kernel_even, hn, mul_neg, Finset.sum_neg_distrib]

theorem solution_odd (m M a b : ℂ) (i : Fin 4) :
    Math.ExteriorOdd.Odd (solution m M a b i) := by
  have hp (j : ℕ) : ∀ i, Math.ExteriorOdd.Odd (((kernel m M a)^j *ᵥ source m M a b) i) := by
    induction j with
    | zero => simpa using source_odd m M a b
    | succ j ih =>
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      exact kernel_preserves_odd m M a _ ih
  simp only [Math.ExteriorOdd.Odd] at hp
  simp only [solution, Math.ExteriorNilpotentKernel.solution,
    Math.ExteriorNilpotentKernel.inverse, Matrix.sum_mulVec, Finset.sum_apply,
    Math.ExteriorOdd.Odd, map_sum, hp, Finset.sum_neg_distrib]

def quadratic (m M a : ℂ) (n : Fin 4 → R) : R :=
  -M • (n 0*n 1) + star M • (n 2*n 3) + (a*star a/m) •
    (-n 0*n 2*cross 1 1+n 0*n 3*cross 1 0+
      n 1*n 2*cross 0 1-n 1*n 3*cross 0 0)

def linear (m a b : ℂ) (n : Fin 4 → R) : R :=
  -(a*b/m) • (n 0*current u d s 1-n 1*current u d s 0) -
    (star a*star b/m) • (n 2*current ub db sb 1-n 3*current ub db sb 0)

def constant (m b : ℂ) : R :=
  (star b*b/m) • ∑ c, downCurrent db sb c * downCurrent d s c

def action (m M a b : ℂ) (n : Fin 4 → R) : R :=
  quadratic m M a n + linear m a b n + constant m b

theorem euler (m M a b : ℂ) (n : Fin 4 → R)
    (hn : ∀ i, Math.ExteriorOdd.Odd (n i)) :
    ∑ i, n i * residual m M a b n i = (2 : ℂ) • quadratic m M a n + linear m a b n := by
  have hs (i j : Fin 4) : n i*n j = -(n j*n i) :=
    Math.ExteriorOdd.anticommute _ _ (hn i) (hn j)
  simp [residual, quadratic, linear, Fin.sum_univ_succ, two_smul,
    mul_add, mul_sub, mul_neg, neg_mul, smul_add, smul_sub,
    ← mul_assoc,
    hs 1 0, hs 2 0, hs 2 1, hs 3 0, hs 3 1, hs 3 2]
  module

theorem eliminated_action (m M a b : ℂ) (hM : M ≠ 0) :
    action m M a b (solution m M a b) =
      (1/2 : ℂ) • linear m a b (solution m M a b) + constant m b := by
  have h := euler m M a b (solution m M a b) (solution_odd m M a b)
  rw [stationary m M a b hM] at h
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h
  have hq : quadratic m M a (solution m M a b) =
      -(1/2 : ℂ) • linear m a b (solution m M a b) := by
    have h' := congrArg (fun x : R => (1/2 : ℂ) • x) h
    simp only [smul_zero, smul_add, smul_smul] at h'
    simp only [show (1/2 : ℂ)*2 = 1 from by norm_num, one_smul] at h'
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h'.symm
  rw [action, hq]
  module

end
end GUT.DevMohapatraHeavyElimination
