import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Simultaneous nonvanishing of any finite valid color contraction graph
on incident vector/covector flags. The proof uses polynomial domains and an
infinite-field specialization, without expanding any content or rank table. -/
namespace Math.ColorFlagNonvanishing
set_option autoImplicit false
noncomputable section

variable {J R : Type*} [CommRing R]

def vector (a : J × Fin 3 → R) (i : J) : Fin 3 → R := ![1,a (i,0),a (i,1)]
def covector (a : J × Fin 3 → R) (i : J) : Fin 3 → R :=
  ![-a (i,2)*a (i,0)-a (i,1),a (i,2),1]
def pair (a : J × Fin 3 → R) (i j : J) : R := ∑ k, covector a i k * vector a j k
def determinant (v : J → Fin 3 → R) (i : Fin 3 → J) : R :=
  Matrix.det (Matrix.of (fun k l => v (i l) k))

theorem incident (a : J × Fin 3 → R) (i : J) : pair a i i = 0 := by
  simp [pair,vector,covector,Fin.sum_univ_succ]

theorem determinant_eq_zero (v : J → Fin 3 → R) (i : Fin 3 → J)
    (hi : ¬ Function.Injective i) : determinant v i = 0 := by
  obtain ⟨a,b,hab,hne⟩ := Function.not_injective_iff.mp hi
  apply Matrix.det_zero_of_column_eq hne
  intro k
  change v (i a) k = v (i b) k
  rw [hab]

abbrev Polynomial (J : Type*) := MvPolynomial (J × Fin 3) ℂ
abbrev indeterminates : J × Fin 3 → Polynomial J := MvPolynomial.X

theorem eval_pair (a : J × Fin 3 → ℂ) (i j : J) :
    MvPolynomial.eval a (pair indeterminates i j) = pair a i j := by
  simp [pair,vector,covector,Fin.sum_univ_succ]

theorem eval_vector_det (a : J × Fin 3 → ℂ) (i : Fin 3 → J) :
    MvPolynomial.eval a (determinant (vector indeterminates) i) = determinant (vector a) i := by
  unfold determinant
  rw [Matrix.det_fin_three,Matrix.det_fin_three]
  simp [vector]

theorem eval_covector_det (a : J × Fin 3 → ℂ) (i : Fin 3 → J) :
    MvPolynomial.eval a (determinant (covector indeterminates) i) = determinant (covector a) i := by
  unfold determinant
  rw [Matrix.det_fin_three,Matrix.det_fin_three]
  simp [covector]

theorem pair_ne_zero (i j : J) (hij : i ≠ j) : pair indeterminates i j ≠ 0 := by
  classical
  let a : J × Fin 3 → ℂ := fun x => if x = (j,1) then 1 else 0
  intro hz
  have he := congrArg (MvPolynomial.eval a) hz
  rw [eval_pair,map_zero] at he
  have hv : pair a i j = 1 := by
    simp [pair,vector,covector,a,hij,Fin.sum_univ_succ]
  exact one_ne_zero (hv.symm.trans he)

theorem vector_det_ne_zero (i : Fin 3 → J) (hi : Function.Injective i) :
    determinant (vector indeterminates) i ≠ 0 := by
  classical
  have h01 : i 0 ≠ i 1 := hi.ne (by decide)
  have h02 : i 0 ≠ i 2 := hi.ne (by decide)
  have h12 : i 1 ≠ i 2 := hi.ne (by decide)
  let a : J × Fin 3 → ℂ := fun x =>
    if x.2 = 0 then (if x.1 = i 1 then 1 else 0)
    else if x.2 = 1 then (if x.1 = i 2 then 1 else 0) else 0
  intro hz
  have he := congrArg (MvPolynomial.eval a) hz
  rw [eval_vector_det,map_zero] at he
  have hv : determinant (vector a) i = 1 := by
    unfold determinant
    rw [Matrix.det_fin_three]
    simp [vector,a,h01,h02,h12,h12.symm]
  exact one_ne_zero (hv.symm.trans he)

theorem covector_det_ne_zero (i : Fin 3 → J) (hi : Function.Injective i) :
    determinant (covector indeterminates) i ≠ 0 := by
  classical
  have h01 : i 0 ≠ i 1 := hi.ne (by decide)
  have h02 : i 0 ≠ i 2 := hi.ne (by decide)
  have h12 : i 1 ≠ i 2 := hi.ne (by decide)
  let a : J × Fin 3 → ℂ := fun x =>
    if x.2 = 1 then (if x.1 = i 1 then -1 else 0)
    else if x.2 = 2 then (if x.1 = i 2 then 1 else 0) else 0
  intro hz
  have he := congrArg (MvPolynomial.eval a) hz
  rw [eval_covector_det,map_zero] at he
  have hv : determinant (covector a) i = 1 := by
    unfold determinant
    rw [Matrix.det_fin_three]
    simp [covector,a,h01,h02,h12,h12.symm]
  exact one_ne_zero (hv.symm.trans he)

variable {P T U : Type*} [Fintype P] [Fintype T] [Fintype U]

def value (a : J × Fin 3 → R) (p : P → J × J)
    (t : T → Fin 3 → J) (u : U → Fin 3 → J) : R :=
  (∏ e, pair a (p e).1 (p e).2) *
    (∏ e, determinant (vector a) (t e)) * (∏ e, determinant (covector a) (u e))

theorem polynomial_ne_zero (p : P → J × J) (t : T → Fin 3 → J) (u : U → Fin 3 → J)
    (hp : ∀ e, (p e).1 ≠ (p e).2) (ht : ∀ e, Function.Injective (t e))
    (hu : ∀ e, Function.Injective (u e)) : value indeterminates p t u ≠ 0 := by
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun e _ => pair_ne_zero _ _ (hp e))
    · exact Finset.prod_ne_zero_iff.mpr (fun e _ => vector_det_ne_zero _ (ht e))
  · exact Finset.prod_ne_zero_iff.mpr (fun e _ => covector_det_ne_zero _ (hu e))

theorem eval_value (a : J × Fin 3 → ℂ) (p : P → J × J)
    (t : T → Fin 3 → J) (u : U → Fin 3 → J) :
    MvPolynomial.eval a (value indeterminates p t u) = value a p t u := by
  simp only [value,map_mul,map_prod,eval_pair,eval_vector_det,eval_covector_det]

/-- Every finite valid diagram has a simultaneous incident-flag witness. -/
theorem exists_nonzero (p : P → J × J) (t : T → Fin 3 → J) (u : U → Fin 3 → J)
    (hp : ∀ e, (p e).1 ≠ (p e).2) (ht : ∀ e, Function.Injective (t e))
    (hu : ∀ e, Function.Injective (u e)) :
    ∃ a : J × Fin 3 → ℂ, value a p t u ≠ 0 := by
  by_contra! h
  apply polynomial_ne_zero p t u hp ht hu
  apply MvPolynomial.funext
  intro a
  rw [eval_value,map_zero,h a]

def functional (a : J × Fin 3 → ℂ) (i : J) : Module.Dual ℂ (Fin 3 → ℂ) :=
  ∑ k, covector a i k • LinearMap.proj k

theorem functional_apply (a : J × Fin 3 → ℂ) (i : J) (v : Fin 3 → ℂ) :
    functional a i v = ∑ k, covector a i k * v k := by
  simp only [functional,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul]

theorem functional_incident (a : J × Fin 3 → ℂ) (i : J) :
    functional a i (vector a i) = 0 := by
  rw [functional_apply]
  exact incident a i

theorem vector_ne_zero (a : J × Fin 3 → ℂ) (i : J) : vector a i ≠ 0 := by
  intro hz
  have he := congrFun hz 0
  exact one_ne_zero he

theorem functional_ne_zero (a : J × Fin 3 → ℂ) (i : J) : functional a i ≠ 0 := by
  intro hz
  have he := LinearMap.congr_fun hz (Pi.single (2 : Fin 3) 1)
  have hv : functional a i (Pi.single (2 : Fin 3) 1) = 1 := by
    simp [functional_apply,covector,Fin.sum_univ_succ]
  exact one_ne_zero (hv.symm.trans he)

/-- A positive criterion for the flag evaluation itself. Its transport to
the actual restricted color sources is a separate semantic obligation. -/
theorem nonzero_iff (p : P → J × J) (t : T → Fin 3 → J) (u : U → Fin 3 → J) :
    (∃ a : J × Fin 3 → ℂ, value a p t u ≠ 0) ↔
      (∀ e, (p e).1 ≠ (p e).2) ∧
        (∀ e, Function.Injective (t e)) ∧ (∀ e, Function.Injective (u e)) := by
  classical
  constructor
  · rintro ⟨a,ha⟩
    have hp : ∀ e, (p e).1 ≠ (p e).2 := by
      intro e he
      apply ha
      have hz : pair a (p e).1 (p e).2 = 0 := by rw [he]; exact incident a _
      have hp0 : (∏ d, pair a (p d).1 (p d).2) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ e) hz
      simp only [value,hp0,zero_mul]
    have ht : ∀ e, Function.Injective (t e) := by
      intro e
      by_contra he
      apply ha
      have ht0 : (∏ d, determinant (vector a) (t d)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ e) (determinant_eq_zero _ _ he)
      simp only [value,ht0,mul_zero,zero_mul]
    have hu : ∀ e, Function.Injective (u e) := by
      intro e
      by_contra he
      apply ha
      have hu0 : (∏ d, determinant (covector a) (u d)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ e) (determinant_eq_zero _ _ he)
      simp only [value,hu0,mul_zero]
    exact ⟨hp,ht,hu⟩
  · rintro ⟨hp,ht,hu⟩
    exact exists_nonzero p t u hp ht hu

end
end Math.ColorFlagNonvanishing
