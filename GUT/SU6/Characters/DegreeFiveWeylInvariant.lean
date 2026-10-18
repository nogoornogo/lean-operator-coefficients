import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Degree-five Weyl invariants on the trace-zero Cartan

The Weyl group of `SU(6)` permutes the six diagonal Cartan coordinates.  This
file proves the invariant-theory fact needed by the fifth-moment hypercharge
argument: every symmetric homogeneous polynomial of degree five, restricted
to the trace-zero hyperplane, is a rational linear combination of the fifth
power sum and the product of the second and third power sums.

The proof uses mathlib's fundamental theorem of symmetric polynomials.  It
grades the six elementary-symmetric generators by degrees `1,...,6`, kills
the first generator on the trace-zero hyperplane, and classifies the two
remaining generator monomials of total weight five.  Newton identities then
convert `e5` and `e2*e3` to the power-sum basis.
-/

open scoped BigOperators

namespace GUT
namespace DegreeFiveWeylInvariant

open Finset
open MvPolynomial

noncomputable section

private theorem card_fin_six : Fintype.card (Fin 6) = 6 := by simp

variable {R : Type*} [CommRing R]
variable {σ : Type*} [Fintype σ]

theorem esymm_isHomogeneous' (k : ℕ) :
    (esymm σ R k).IsHomogeneous k := by
  rw [esymm]
  apply IsHomogeneous.sum
  intro s hs
  rw [mem_powersetCard] at hs
  have hp := IsHomogeneous.prod s (fun i => X (R := R) i)
    (fun _ => 1) (fun i _ => MvPolynomial.isHomogeneous_X (R := R) i)
  simpa [hs.2] using hp

/-- The ordinary polynomial degree of the corresponding elementary
symmetric generator. -/
def generatorWeight (i : Fin 6) : ℕ := i + 1

/-- Substitute the six elementary symmetric polynomials for six formal
generators. -/
def elementaryImage (q : MvPolynomial (Fin 6) R) :
    MvPolynomial (Fin 6) R :=
  (esymmAlgHom (Fin 6) R 6 q).1

@[simp]
theorem elementaryImage_zero :
    elementaryImage (R := R) 0 = 0 := by
  simp [elementaryImage]

@[simp]
theorem elementaryImage_add (p q : MvPolynomial (Fin 6) R) :
    elementaryImage (p + q) = elementaryImage p + elementaryImage q := by
  simp [elementaryImage]

theorem elementaryImage_monomial_isHomogeneous
    (d : Fin 6 →₀ ℕ) (c : R) :
    (elementaryImage (monomial d c)).IsHomogeneous
      (Finsupp.weight generatorWeight d) := by
  rw [elementaryImage, esymmAlgHom_apply, aeval_monomial]
  apply IsHomogeneous.C_mul
  have hp := IsHomogeneous.prod d.support
    (fun i => esymm (Fin 6) R (i + 1) ^ d i)
    (fun i => (i + 1) * d i)
    (fun i _ => (esymm_isHomogeneous' (R := R) (σ := Fin 6) (i + 1)).pow (d i))
  simpa [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, generatorWeight,
    nsmul_eq_mul, mul_comm] using hp

theorem homogeneousComponent_elementaryImage
    (k : ℕ) (q : MvPolynomial (Fin 6) R) :
    homogeneousComponent k (elementaryImage q) =
      elementaryImage
        (weightedHomogeneousComponent generatorWeight k q) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
  | monomial d c =>
      rw [homogeneousComponent_of_mem
        (elementaryImage_monomial_isHomogeneous (R := R) d c)]
      rw [weightedHomogeneousComponent_of_mem
        (isWeightedHomogeneous_monomial generatorWeight d c rfl)]
      by_cases hk : k = Finsupp.weight generatorWeight d
      · simp [hk]
      · simp [hk]

/-- Once the degree-one generator is absent, the only generator monomials
of weighted degree five are `e5` and `e2*e3`. -/
theorem weight_five_of_zero_first
    (d : Fin 6 →₀ ℕ)
    (hWeight : Finsupp.weight generatorWeight d = 5)
    (hZero : d 0 = 0) :
    d = Finsupp.single 4 1 ∨
      d = Finsupp.single 1 1 + Finsupp.single 2 1 := by
  rw [Finsupp.weight_eq_sum] at hWeight
  simp [generatorWeight, Fin.sum_univ_succ, hZero] at hWeight
  by_cases hFour : d 4 = 0
  · right
    ext i
    fin_cases i <;> simp_all <;> omega
  · left
    ext i
    fin_cases i <;> simp_all <;> omega

/-- Substitution which sets the degree-one elementary generator to zero. -/
def killFirst (i : Fin 6) : MvPolynomial (Fin 6) R :=
  if i = 0 then 0 else X i

theorem killFirst_weightFive_shape
    (q : MvPolynomial (Fin 6) R)
    (hq : q.IsWeightedHomogeneous generatorWeight 5) :
    ∃ A B : R,
      aeval (killFirst (R := R)) q =
        C A * X 4 + C B * (X 1 * X 2) := by
  induction hq using IsWeightedHomogeneous.induction_on with
  | zero =>
      exact ⟨0, 0, by simp⟩
  | add p q hp hq ihp ihq =>
      rcases ihp with ⟨A, B, hp⟩
      rcases ihq with ⟨C', D, hq⟩
      refine ⟨A + C', B + D, ?_⟩
      rw [map_add, hp, hq]
      simp only [map_add]
      ring
  | monomial d c hd =>
      by_cases hZero : d 0 = 0
      · rcases weight_five_of_zero_first d hd hZero with h | h
        · subst d
          refine ⟨c, 0, ?_⟩
          rw [aeval_monomial]
          simp [killFirst, Finsupp.prod]
        · subst d
          refine ⟨0, c, ?_⟩
          rw [monomial_add_single, ← C_mul_X_eq_monomial, map_mul, map_mul]
          simp [killFirst]
          ring
      · refine ⟨0, 0, ?_⟩
        rw [aeval_monomial]
        have hProd :
            (d.prod fun i n => killFirst (R := R) i ^ n) = 0 := by
          rw [Finsupp.prod]
          apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hZero)
          simp [killFirst, hZero]
        rw [hProd]
        simp

theorem symmetric_homogeneous_elementaryImage_weightFive
    (p : MvPolynomial (Fin 6) R)
    (hSym : p.IsSymmetric) (hHom : p.IsHomogeneous 5) :
    let q := (esymmAlgEquiv (n := 6) (Fin 6) R card_fin_six).symm ⟨p, hSym⟩
    elementaryImage
        (weightedHomogeneousComponent generatorWeight 5 q) = p := by
  dsimp only
  let q := (esymmAlgEquiv (n := 6) (Fin 6) R card_fin_six).symm ⟨p, hSym⟩
  have hEq : elementaryImage q = p := by
    change ((esymmAlgEquiv (n := 6) (Fin 6) R card_fin_six) q).1 = p
    dsimp [q]
    exact congrArg Subtype.val
      ((esymmAlgEquiv (n := 6) (Fin 6) R card_fin_six).apply_symm_apply ⟨p, hSym⟩)
  have hc := homogeneousComponent_elementaryImage (R := R) 5 q
  rw [hEq, homogeneousComponent_eq_self hHom] at hc
  simpa [q] using hc.symm

theorem two_esymm_two :
    2 * esymm (Fin 6) R 2 =
      esymm (Fin 6) R 1 * psum (Fin 6) R 1 - psum (Fin 6) R 2 := by
  have hn := mul_esymm_eq_sum (Fin 6) R 2
  have had : {a ∈ Finset.antidiagonal 2 | a.1 < 2} =
      ({(0, 2), (1, 1)} : Finset (ℕ × ℕ)) := by decide
  rw [had] at hn
  norm_num at hn
  simp [esymm_one, psum_one] at hn ⊢
  linear_combination hn

theorem three_esymm_three :
    3 * esymm (Fin 6) R 3 =
      esymm (Fin 6) R 2 * psum (Fin 6) R 1 -
        esymm (Fin 6) R 1 * psum (Fin 6) R 2 + psum (Fin 6) R 3 := by
  have hn := mul_esymm_eq_sum (Fin 6) R 3
  have had : {a ∈ Finset.antidiagonal 3 | a.1 < 3} =
      ({(0, 3), (1, 2), (2, 1)} : Finset (ℕ × ℕ)) := by decide
  rw [had] at hn
  norm_num at hn
  simp [esymm_one, psum_one] at hn ⊢
  linear_combination hn

theorem five_esymm_five :
    5 * esymm (Fin 6) R 5 =
      esymm (Fin 6) R 4 * psum (Fin 6) R 1 -
        esymm (Fin 6) R 3 * psum (Fin 6) R 2 +
        esymm (Fin 6) R 2 * psum (Fin 6) R 3 -
        esymm (Fin 6) R 1 * psum (Fin 6) R 4 + psum (Fin 6) R 5 := by
  have hn := mul_esymm_eq_sum (Fin 6) R 5
  have had : {a ∈ Finset.antidiagonal 5 | a.1 < 5} =
      ({(0, 5), (1, 4), (2, 3), (3, 2), (4, 1)} : Finset (ℕ × ℕ)) := by
    decide
  rw [had] at hn
  norm_num at hn
  simp [esymm_one, psum_one] at hn ⊢
  linear_combination hn

/-- Values of `e1,...,e6` at a Cartan point, indexed from zero. -/
def elementaryValue (x : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  eval x (esymm (Fin 6) ℚ (i + 1))

/-- The `k`-th power sum of six Cartan coordinates. -/
def powerSumValue (x : Fin 6 → ℚ) (k : ℕ) : ℚ :=
  ∑ i, x i ^ k

@[simp]
theorem eval_psum (x : Fin 6 → ℚ) (k : ℕ) :
    eval x (psum (Fin 6) ℚ k) = powerSumValue x k := by
  simp [psum, powerSumValue]

theorem eval_elementaryImage (x : Fin 6 → ℚ)
    (q : MvPolynomial (Fin 6) ℚ) :
    eval x (elementaryImage q) = eval (elementaryValue x) q := by
  rw [elementaryImage, esymmAlgHom_apply]
  change aeval x (bind₁ (fun i : Fin 6 ↦ esymm (Fin 6) ℚ (i + 1)) q) = _
  rw [aeval_bind₁]
  rfl

theorem elementaryValue_zero_of_sum_eq_zero
    (x : Fin 6 → ℚ) (hx : ∑ i, x i = 0) :
    elementaryValue x 0 = 0 := by
  simp [elementaryValue, esymm_one, hx]

theorem elementaryValue_one_of_sum_eq_zero
    (x : Fin 6 → ℚ) (hx : ∑ i, x i = 0) :
    elementaryValue x 1 = -(powerSumValue x 2) / 2 := by
  have hn := congrArg (eval x) (two_esymm_two (R := ℚ))
  simp [elementaryValue, powerSumValue, hx] at hn ⊢
  linarith

theorem elementaryValue_two_of_sum_eq_zero
    (x : Fin 6 → ℚ) (hx : ∑ i, x i = 0) :
    elementaryValue x 2 = powerSumValue x 3 / 3 := by
  have hn := congrArg (eval x) (three_esymm_three (R := ℚ))
  simp [elementaryValue, powerSumValue, hx] at hn ⊢
  linarith

theorem elementaryValue_four_of_sum_eq_zero
    (x : Fin 6 → ℚ) (hx : ∑ i, x i = 0) :
    elementaryValue x 4 =
      powerSumValue x 5 / 5 -
        powerSumValue x 2 * powerSumValue x 3 / 6 := by
  have hn := congrArg (eval x) (five_esymm_five (R := ℚ))
  simp [hx] at hn
  change 5 * elementaryValue x 4 =
    -(elementaryValue x 2 * powerSumValue x 2) +
      elementaryValue x 1 * powerSumValue x 3 + powerSumValue x 5 at hn
  rw [elementaryValue_one_of_sum_eq_zero x hx,
    elementaryValue_two_of_sum_eq_zero x hx] at hn
  nlinarith

/-- Every symmetric homogeneous polynomial of degree five in six variables
restricts to the span of `p5` and `p2*p3` on the trace-zero hyperplane. -/
theorem symmetric_degreeFive_traceZero_span
    (p : MvPolynomial (Fin 6) ℚ)
    (hSym : p.IsSymmetric) (hHom : p.IsHomogeneous 5) :
    ∃ A B : ℚ, ∀ x : Fin 6 → ℚ, (∑ i, x i) = 0 →
      eval x p = A * powerSumValue x 5 +
        B * (powerSumValue x 2 * powerSumValue x 3) := by
  let q := (esymmAlgEquiv (n := 6) (Fin 6) ℚ card_fin_six).symm ⟨p, hSym⟩
  let q5 := weightedHomogeneousComponent generatorWeight 5 q
  have hImage : elementaryImage q5 = p := by
    simpa [q, q5] using
      symmetric_homogeneous_elementaryImage_weightFive p hSym hHom
  have hq5 : q5.IsWeightedHomogeneous generatorWeight 5 := by
    exact weightedHomogeneousComponent_isWeightedHomogeneous (w := generatorWeight) 5 q
  rcases killFirst_weightFive_shape q5 hq5 with ⟨A, B, hShape⟩
  refine ⟨A / 5, -(A + B) / 6, ?_⟩
  intro x hx
  let e := elementaryValue x
  have he0 : e 0 = 0 := by
    exact elementaryValue_zero_of_sum_eq_zero x hx
  have hAssignment : (fun i ↦ aeval e (killFirst (R := ℚ) i)) = e := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [killFirst, he0]
    · simp [killFirst, hi]
  have hKill : eval e (aeval (killFirst (R := ℚ)) q5) = eval e q5 := by
    change aeval e (bind₁ (killFirst (R := ℚ)) q5) = _
    rw [aeval_bind₁, hAssignment]
    rfl
  have he1 : e 1 = -(powerSumValue x 2) / 2 := by
    exact elementaryValue_one_of_sum_eq_zero x hx
  have he2 : e 2 = powerSumValue x 3 / 3 := by
    exact elementaryValue_two_of_sum_eq_zero x hx
  have he4 : e 4 = powerSumValue x 5 / 5 -
      powerSumValue x 2 * powerSumValue x 3 / 6 := by
    exact elementaryValue_four_of_sum_eq_zero x hx
  calc
    eval x p = eval x (elementaryImage q5) := by rw [hImage]
    _ = eval e q5 := eval_elementaryImage x q5
    _ = eval e (aeval (killFirst (R := ℚ)) q5) := hKill.symm
    _ = eval e (C A * X 4 + C B * (X 1 * X 2)) := by rw [hShape]
    _ = A * e 4 + B * (e 1 * e 2) := by simp
    _ = (A / 5) * powerSumValue x 5 +
        (-(A + B) / 6) * (powerSumValue x 2 * powerSumValue x 3) := by
      rw [he1, he2, he4]
      ring

end
end DegreeFiveWeylInvariant
end GUT
