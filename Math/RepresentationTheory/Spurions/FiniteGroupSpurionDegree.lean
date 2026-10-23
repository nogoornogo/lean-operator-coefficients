import Math.RepresentationTheory.Spurions.FiniteGroupSpurionCoefficients
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Total-degree bounds for finite-group polynomial covariant evaluation. -/
namespace Math.PolynomialCovariantEvaluation
noncomputable section
open scoped BigOperators
open MvPolynomial Representation
variable {I J H : Type*}
local instance : DecidableEq (I → ℂ) := Classical.decEq _

/-- A uniform bound on the total degree of each target coordinate. -/
def DegreeLE (p : Polynomials (I := I) (J := J)) (d : ℕ) : Prop :=
  ∀ j, (p j).totalDegree ≤ d

section BoundedSpace
variable [Group H] (a : Representation ℂ H (I → ℂ))
  (b : Representation ℂ H (J → ℂ))

/-- Polynomial covariants restricted to a fixed total-degree bound. -/
def boundedCovariants (d : ℕ) : Submodule ℂ (covariants a b) where
  carrier := {p | DegreeLE p.val d}
  zero_mem' := by intro j; simp
  add_mem' := by
    intro p q hp hq j
    exact (totalDegree_add _ _).trans (max_le (hp j) (hq j))
  smul_mem' := by
    intro z p hp j
    exact (totalDegree_smul_le z (p.val j)).trans (hp j)

/-- Restrict the existing evaluation map to covariants of bounded degree. -/
def boundedEvaluation (s : I → ℂ) (d : ℕ) :
    boundedCovariants a b d →ₗ[ℂ]
      Representation.invariants (b.comp (stabilizer a s).subtype) :=
  (evaluation a b s).comp (boundedCovariants a b d).subtype
end BoundedSpace

/-- The separating polynomial can be chosen linear. -/
theorem exists_separator_bounded (t u : I → ℂ) (h : t ≠ u) :
    ∃ p : MvPolynomial I ℂ, eval t p = 1 ∧ eval u p = 0 ∧ p.totalDegree ≤ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  refine ⟨C ((t i - u i)⁻¹) * (X i - C (u i)), ?_, ?_, ?_⟩
  · simp [sub_ne_zero.mpr hi]
  · simp
  · calc
      _ ≤ (C ((t i - u i)⁻¹) : MvPolynomial I ℂ).totalDegree +
          (X i - C (u i)).totalDegree := totalDegree_mul _ _
      _ ≤ 1 := by
        simpa using (totalDegree_sub_C_le (X i : MvPolynomial I ℂ) (u i))

/-- A delta polynomial needs at most one linear factor per other point. -/
theorem exists_delta_bounded (O : Finset (I → ℂ)) (t : I → ℂ) (ht : t ∈ O) :
    ∃ p : MvPolynomial I ℂ,
      (∀ u ∈ O, eval u p = if u = t then 1 else 0) ∧
      p.totalDegree ≤ O.card - 1 := by
  classical
  have sep : ∀ u : {u // u ∈ O.erase t}, ∃ p : MvPolynomial I ℂ,
      eval t p = 1 ∧ eval u.val p = 0 ∧ p.totalDegree ≤ 1 := by
    intro u
    exact exists_separator_bounded t u.val (Ne.symm (Finset.mem_erase.mp u.property).1)
  choose p hp using sep
  refine ⟨∏ u : {u // u ∈ O.erase t}, p u, ?_, ?_⟩
  · intro u hu
    by_cases hut : u = t
    · subst u
      simp [(fun u => (hp u).1)]
    · rw [ite_eq_right hut, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨u, Finset.mem_erase.mpr ⟨hut, hu⟩⟩)
        (hp ⟨u, Finset.mem_erase.mpr ⟨hut, hu⟩⟩).2.1
  · calc
      _ ≤ ∑ u : {u // u ∈ O.erase t}, (p u).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ _u : {u // u ∈ O.erase t}, 1 := Finset.sum_le_sum fun u _ => (hp u).2.2
      _ = O.card - 1 := by simp [Finset.card_erase_of_mem ht]

/-- Finite interpolation has degree at most the number of points minus one. -/
theorem finite_interpolation_bounded (O : Finset (I → ℂ))
    (f : (I → ℂ) → (J → ℂ)) :
    ∃ p : Polynomials (I := I) (J := J),
      (∀ t ∈ O, evaluate t p = f t) ∧ DegreeLE p (O.card - 1) := by
  classical
  choose p hp using fun t : {t // t ∈ O} => exists_delta_bounded O t.val t.property
  refine ⟨fun j => ∑ t : {t // t ∈ O}, C (f t.val j) * p t, ?_, ?_⟩
  · intro t ht
    funext j
    simp only [evaluate_apply, eval_sum, eval_mul, eval_C]
    rw [Fintype.sum_eq_single ⟨t, ht⟩]
    · simp [(hp _).1 t ht]
    · intro u hu
      have hne : t ≠ u.val := by
        intro h
        exact hu (Subtype.ext h.symm)
      simp [(hp _).1 t ht, hne]
  · intro j
    apply totalDegree_finsetSum_le
    intro t _
    exact (totalDegree_mul _ _).trans (by simpa using (hp t).2)

/-- Substitution by polynomials of degree at most one cannot increase total degree. -/
theorem totalDegree_bind_linear (q : I → MvPolynomial I ℂ)
    (hq : ∀ i, (q i).totalDegree ≤ 1) (p : MvPolynomial I ℂ) :
    (bind₁ q p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro m hm
  rw [bind₁_monomial]
  calc
    _ ≤ (C (p.coeff m) : MvPolynomial I ℂ).totalDegree +
        (∏ i ∈ m.support, q i ^ m i).totalDegree := totalDegree_mul _ _
    _ = (∏ i ∈ m.support, q i ^ m i).totalDegree := by simp
    _ ≤ ∑ i ∈ m.support, (q i ^ m i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (m i) (hq i))
    _ ≤ p.totalDegree := le_totalDegree hm

section Coordinates
variable [Fintype I] [Fintype J]

omit [Fintype J] in
theorem linearCoordinates_degree (L : (I → ℂ) →ₗ[ℂ] (J → ℂ)) (j : J) :
    (linearCoordinates L j).totalDegree ≤ 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

omit [Fintype J] in
theorem degreeLE_precompose (L : (I → ℂ) →ₗ[ℂ] (I → ℂ))
    (p : Polynomials (I := I) (J := J)) (d : ℕ) (hp : DegreeLE p d) :
    DegreeLE (precompose L p) d := by
  intro j
  exact (totalDegree_bind_linear _ (linearCoordinates_degree L) _).trans (hp j)

omit [Fintype I] in
theorem degreeLE_postcompose (L : (J → ℂ) →ₗ[ℂ] (J → ℂ))
    (p : Polynomials (I := I) (J := J)) (d : ℕ) (hp : DegreeLE p d) :
    DegreeLE (postcompose L p) d := by
  classical
  intro j
  apply totalDegree_finsetSum_le
  intro k _
  exact (totalDegree_mul _ _).trans (by simpa using hp k)
end Coordinates

section FiniteGroup
variable [Group H] [Fintype H] [Fintype I] [Fintype J]
  (a : Representation ℂ H (I → ℂ)) (b : Representation ℂ H (J → ℂ))

/-- Number of distinct points in the actual finite orbit. -/
def orbitSize (s : I → ℂ) : ℕ := (Finset.univ.image (fun g : H => a g s)).card

omit [Fintype I] in
theorem orbitSize_pos (s : I → ℂ) : 0 < orbitSize a s := by
  classical
  exact Finset.card_pos.mpr ⟨s, Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩⟩

omit [Fintype I] in
theorem orbitSize_le_card (s : I → ℂ) : orbitSize a s ≤ Fintype.card H := by
  classical
  exact (Finset.card_image_le).trans_eq (Finset.card_univ)

theorem degreeLE_reynolds (p : Polynomials (I := I) (J := J))
    (d : ℕ) (hp : DegreeLE p d) : DegreeLE (reynolds a b p) d := by
  classical
  intro j
  apply (totalDegree_smul_le _ _).trans
  simp only [Finset.sum_apply]
  apply totalDegree_finsetSum_le
  intro g _
  exact degreeLE_postcompose _ _ d (degreeLE_precompose _ p d hp) j

/-- Every stabilizer-fixed vector has a covariant witness bounded by orbit size. -/
theorem finite_group_bounded (s : I → ℂ)
    (w : Representation.invariants (b.comp (stabilizer a s).subtype)) :
    ∃ p : covariants a b, evaluation a b s p = w ∧
      DegreeLE p.val (orbitSize a s - 1) := by
  classical
  let f := Function.extend (fun g : H => a g s) (fun g => b g w.val) 0
  have hf (g : H) : f (a g s) = b g w.val :=
    (orbit_factors a b s w).extend_apply 0 g
  obtain ⟨p, hp, hd⟩ := finite_interpolation_bounded
    (Finset.univ.image (fun g : H => a g s)) f
  refine ⟨⟨reynolds a b p, reynolds_covariant a b p⟩, ?_, degreeLE_reynolds a b p _ hd⟩
  apply Subtype.ext
  change evaluate s (reynolds a b p) = w.val
  rw [evaluate_reynolds]
  have he (g : H) : b g⁻¹ (evaluate (a g s) p) = w.val := by
    rw [hp _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩), hf]
    simp [← Module.End.mul_apply, ← map_mul]
  simp only [he, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Fintype.card_ne_zero

/-- Group order gives a uniform bound independent of the chosen value. -/
theorem finite_group_card_bounded (s : I → ℂ)
    (w : Representation.invariants (b.comp (stabilizer a s).subtype)) :
    ∃ p : covariants a b, evaluation a b s p = w ∧
      DegreeLE p.val (Fintype.card H - 1) := by
  obtain ⟨p, hp, hd⟩ := finite_group_bounded a b s w
  exact ⟨p, hp, fun j => (hd j).trans (Nat.sub_le_sub_right (orbitSize_le_card a s) 1)⟩
/-- The finite cutoff already has the full evaluation image. -/
theorem boundedEvaluation_surjective (s : I → ℂ) :
    Function.Surjective (boundedEvaluation a b s (orbitSize a s - 1)) := by
  intro w
  obtain ⟨p, hp, hd⟩ := finite_group_bounded a b s w
  exact ⟨⟨p, hd⟩, hp⟩

theorem card_boundedEvaluation_surjective (s : I → ℂ) :
    Function.Surjective (boundedEvaluation a b s (Fintype.card H - 1)) := by
  intro w
  obtain ⟨p, hp, hd⟩ := finite_group_card_bounded a b s w
  exact ⟨⟨p, hd⟩, hp⟩

omit [Fintype I] in
@[simp] theorem orbitSize_zero : orbitSize a (0 : I → ℂ) = 1 := by
  classical
  simp only [orbitSize, map_zero]
  rw [Finset.image_const Finset.univ_nonempty]
  rfl

/-- The zero orbit is a singleton, so constant covariants suffice. -/
theorem zero_degree_bounded
    (w : Representation.invariants (b.comp (stabilizer a (0 : I → ℂ)).subtype)) :
    ∃ p : covariants a b, evaluation a b 0 p = w ∧ DegreeLE p.val 0 := by
  simpa only [orbitSize_zero, Nat.sub_self] using finite_group_bounded a b 0 w
end FiniteGroup

section Coefficients
variable [Group H] [Fintype H] [Fintype I] [Fintype J]
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (a : Representation ℂ H (I → ℂ)) (r : Representation ℂ H V)
  (e : Module.Dual ℂ V ≃ₗ[ℂ] (J → ℂ))

/-- The existing coefficient evaluation restricted to a fixed spurion degree. -/
def boundedCoefficientEvaluation (s : I → ℂ) (d : ℕ) :
    boundedCovariants a (coordinateAction e r.dual) d →ₗ[ℂ]
      IntertwiningMap (r.comp (stabilizer a s).subtype)
        (trivial ℂ (stabilizer a s) ℂ) :=
  (coefficientEvaluation a r e s).comp
    (boundedCovariants a (coordinateAction e r.dual) d).subtype

/-- Every residual coefficient is realized within the orbit-size degree cutoff. -/
theorem boundedCoefficientEvaluation_surjective (s : I → ℂ) :
    Function.Surjective (boundedCoefficientEvaluation a r e s (orbitSize a s - 1)) :=
  (fixedDualEquiv r e (stabilizer a s)).surjective.comp
    (boundedEvaluation_surjective a (coordinateAction e r.dual) s)

theorem card_boundedCoefficientEvaluation_surjective (s : I → ℂ) :
    Function.Surjective (boundedCoefficientEvaluation a r e s (Fintype.card H - 1)) :=
  (fixedDualEquiv r e (stabilizer a s)).surjective.comp
    (card_boundedEvaluation_surjective a (coordinateAction e r.dual) s)

/-- Finite dimensionality supplies the dual basis without an extra premise. -/
theorem finite_dimensional_bounded_coefficients [FiniteDimensional ℂ V] (s : I → ℂ) :
    Function.Surjective (boundedCoefficientEvaluation a r
      (Module.finBasis ℂ (Module.Dual ℂ V)).equivFun s (orbitSize a s - 1)) :=
  boundedCoefficientEvaluation_surjective a r _ s
end Coefficients
end
end Math.PolynomialCovariantEvaluation
