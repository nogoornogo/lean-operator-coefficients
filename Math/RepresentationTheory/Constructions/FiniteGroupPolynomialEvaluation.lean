import Math.RepresentationTheory.Invariants.PolynomialCovariantEvaluation
import Mathlib.Algebra.MvPolynomial.Monad

/-! Finite-orbit interpolation and finite-group covariant evaluation. -/
namespace Math.PolynomialCovariantEvaluation
noncomputable section
open scoped BigOperators
open MvPolynomial Representation

variable {I J H : Type*}
local instance : DecidableEq (I → ℂ) := Classical.decEq _

/-- Distinct coordinate vectors can be separated by a linear polynomial. -/
theorem exists_separator (t u : I → ℂ) (h : t ≠ u) :
    ∃ p : MvPolynomial I ℂ, eval t p = 1 ∧ eval u p = 0 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  refine ⟨C ((t i - u i)⁻¹) * (X i - C (u i)), ?_, ?_⟩
  · simp [sub_ne_zero.mpr hi]
  · simp

/-- Delta interpolation on any finite set of coordinate vectors. -/
theorem exists_delta (O : Finset (I → ℂ)) (t : I → ℂ) :
    ∃ p : MvPolynomial I ℂ, ∀ u ∈ O, eval u p = if u = t then 1 else 0 := by
  classical
  have sep : ∀ u : {u // u ∈ O.erase t}, ∃ p : MvPolynomial I ℂ,
      eval t p = 1 ∧ eval u.val p = 0 := by
    intro u
    exact exists_separator t u.val (Ne.symm (Finset.mem_erase.mp u.property).1)
  choose p hp using sep
  refine ⟨∏ u : {u // u ∈ O.erase t}, p u, ?_⟩
  intro u hu
  by_cases hut : u = t
  · subst u
    simp [(fun u => (hp u).1)]
  · rw [ite_eq_right hut, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ ⟨u, Finset.mem_erase.mpr ⟨hut, hu⟩⟩)
      (hp ⟨u, Finset.mem_erase.mpr ⟨hut, hu⟩⟩).2

/-- Arbitrary vector data on a finite set have coordinate-polynomial extensions. -/
theorem finite_interpolation (O : Finset (I → ℂ)) (f : (I → ℂ) → (J → ℂ)) :
    ∃ p : Polynomials (I := I) (J := J), ∀ t ∈ O, evaluate t p = f t := by
  classical
  choose p hp using fun t : {t // t ∈ O} => exists_delta O t.val
  refine ⟨fun j => ∑ t : {t // t ∈ O}, C (f t.val j) * p t, ?_⟩
  intro t ht
  funext j
  simp only [evaluate_apply, eval_sum, eval_mul, eval_C]
  rw [Fintype.sum_eq_single ⟨t, ht⟩]
  · simp [hp _ t ht]
  · intro u hu
    have hne : t ≠ u.val := by
      intro h
      exact hu (Subtype.ext h.symm)
    simp [hp _ t ht, hne]

section Coordinates
variable [Fintype I] [Fintype J]

/-- Coordinates of a linear map represented by linear polynomials. -/
def linearCoordinates (L : (I → ℂ) →ₗ[ℂ] (J → ℂ)) : J → MvPolynomial I ℂ :=
  by
  classical
  exact fun j => ∑ i, C (L (Pi.single i 1) j) * X i

omit [Fintype J] in
@[simp] theorem eval_linearCoordinates (L : (I → ℂ) →ₗ[ℂ] (J → ℂ))
    (x : I → ℂ) (j : J) : eval x (linearCoordinates L j) = L x j := by
  classical
  have hx : x = ∑ i, x i • Pi.single i (1 : ℂ) := by
    funext i
    simp [Pi.single_apply]
  simp only [linearCoordinates, eval_sum, eval_mul, eval_C, eval_X]
  conv_rhs => rw [hx]
  simp [map_sum, mul_comm]

/-- Precomposition by a linear map preserves coordinate polynomials. -/
def precompose (L : (I → ℂ) →ₗ[ℂ] (I → ℂ))
    (p : Polynomials (I := I) (J := J)) : Polynomials (I := I) (J := J) :=
  fun j => bind₁ (linearCoordinates L) (p j)

omit [Fintype J] in
@[simp] theorem evaluate_precompose (L : (I → ℂ) →ₗ[ℂ] (I → ℂ))
    (p : Polynomials (I := I) (J := J)) (x : I → ℂ) :
    evaluate x (precompose L p) = evaluate (L x) p := by
  funext j
  change aeval x (bind₁ (linearCoordinates L) (p j)) = _
  rw [aeval_bind₁]
  simp only [aeval_eq_eval, eval_linearCoordinates]
  rfl

/-- Postcomposition by a linear map preserves coordinate polynomials. -/
def postcompose (L : (J → ℂ) →ₗ[ℂ] (J → ℂ))
    (p : Polynomials (I := I) (J := J)) : Polynomials (I := I) (J := J) :=
  by
  classical
  exact fun j => ∑ k, C (L (Pi.single k 1) j) * p k

omit [Fintype I] in
@[simp] theorem evaluate_postcompose (L : (J → ℂ) →ₗ[ℂ] (J → ℂ))
    (p : Polynomials (I := I) (J := J)) (x : I → ℂ) :
    evaluate x (postcompose L p) = L (evaluate x p) := by
  funext j
  have h := eval_linearCoordinates L (evaluate x p) j
  simpa [evaluate_apply, postcompose, linearCoordinates, eval_sum] using h
end Coordinates
section FiniteGroup
variable [Group H] [Fintype H] [Fintype I] [Fintype J]
  (a : Representation ℂ H (I → ℂ)) (b : Representation ℂ H (J → ℂ))

/-- Reynolds averaging of a coordinate polynomial map. -/
def reynolds (p : Polynomials (I := I) (J := J)) :
    Polynomials (I := I) (J := J) :=
  (Fintype.card H : ℂ)⁻¹ • ∑ g : H, postcompose (b g⁻¹) (precompose (a g) p)

theorem evaluate_reynolds (p : Polynomials (I := I) (J := J)) (x : I → ℂ) :
    evaluate x (reynolds a b p) =
      (Fintype.card H : ℂ)⁻¹ • ∑ g : H, b g⁻¹ (evaluate (a g x) p) := by
  simp [reynolds, map_sum]

theorem reynolds_covariant (p : Polynomials (I := I) (J := J)) :
    reynolds a b p ∈ covariants a b := by
  intro h x
  rw [evaluate_reynolds, evaluate_reynolds, map_smul, map_sum]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulRight h)
  intro g
  simp [map_mul, Module.End.mul_apply]

omit [Fintype H] [Fintype I] [Fintype J] in
/-- Consistent orbit values from a stabilizer-fixed vector. -/
theorem orbit_factors (s : I → ℂ)
    (w : Representation.invariants (b.comp (stabilizer a s).subtype)) :
    (fun g : H => b g w.val).FactorsThrough (fun g => a g s) := by
  intro g h he
  change a g s = a h s at he
  have hs : h⁻¹ * g ∈ stabilizer a s := by
    change a (h⁻¹ * g) s = s
    rw [map_mul, Module.End.mul_apply, he]
    simp [← Module.End.mul_apply, ← map_mul]
  have hw := w.property ⟨h⁻¹ * g, hs⟩
  change b (h⁻¹ * g) w.val = w.val at hw
  have hh := congrArg (fun v => b h v) hw
  simpa [← Module.End.mul_apply, ← map_mul] using hh

/-- Every fixed vector of the actual stabilizer is a polynomial evaluation. -/
theorem finite_group_surjective (s : I → ℂ) :
    Function.Surjective (evaluation a b s) := by
  classical
  intro w
  let f := Function.extend (fun g : H => a g s) (fun g => b g w.val) 0
  have hf (g : H) : f (a g s) = b g w.val :=
    (orbit_factors a b s w).extend_apply 0 g
  obtain ⟨p, hp⟩ := finite_interpolation (Finset.univ.image (fun g : H => a g s)) f
  refine ⟨⟨reynolds a b p, reynolds_covariant a b p⟩, ?_⟩
  apply Subtype.ext
  change evaluate s (reynolds a b p) = w.val
  rw [evaluate_reynolds]
  have he (g : H) : b g⁻¹ (evaluate (a g s) p) = w.val := by
    rw [hp _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩), hf]
    simp [← Module.End.mul_apply, ← map_mul]
  simp only [he, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero
end FiniteGroup
end
end Math.PolynomialCovariantEvaluation
