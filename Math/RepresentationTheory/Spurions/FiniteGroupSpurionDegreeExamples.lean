import Math.RepresentationTheory.Spurions.FiniteGroupSpurionDegree
import Math.RepresentationTheory.Spurions.FiniteGroupSpurionExamples

/-! Degree-cutoff controls on the finite permutation example. -/
namespace Math.PolynomialCovariantEvaluation
noncomputable section
open MvPolynomial Representation

/-- Degree zero means the coordinate-polynomial map is constant everywhere. -/
theorem degree_zero_evaluation_eq {I J : Type*}
    (p : Polynomials (I := I) (J := J)) (hp : DegreeLE p 0) (x y : I → ℂ) :
    evaluate x p = evaluate y p := by
  funext j
  simp only [evaluate_apply]
  rw [totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hp j))]
  simp

namespace FiniteControls

/-- The two-point permutation group requires no covariant above degree one. -/
theorem free_value_degree_one (w : V) :
    ∃ p : covariants action action, evaluate value p.val = w ∧ DegreeLE p.val 1 := by
  have hw : w ∈ Representation.invariants (action.comp (stabilizer action value).subtype) := by
    intro g
    change action g.val w = w
    rw [value_stabilizer g.val g.property]
    simp
  obtain ⟨p, hp, hd⟩ := finite_group_card_bounded action action value ⟨w, hw⟩
  have hcard : Fintype.card H = 2 := by simp [H, Fintype.card_perm]
  exact ⟨p, congrArg Subtype.val hp, by simpa only [hcard] using hd⟩

/-- In this example degree zero cannot replace degree one. -/
theorem free_value_not_degree_zero : ¬ ∃ p : covariants action action,
    evaluate value p.val = value ∧ DegreeLE p.val 0 := by
  rintro ⟨p, hp, hd⟩
  apply zero_not_attains_value
  exact ⟨p, (degree_zero_evaluation_eq p.val hd 0 value).trans hp⟩

/-- The singleton zero orbit already attains its invariant target at degree zero. -/
theorem zero_constant_degree_zero : ∃ p : covariants action action,
    evaluate (0 : V) p.val = (fun _ => 1) ∧ DegreeLE p.val 0 := by
  have hw : (fun _ : Fin 2 => (1 : ℂ)) ∈
      Representation.invariants (action.comp (stabilizer action (0 : V)).subtype) := by
    intro g
    rfl
  obtain ⟨p, hp, hd⟩ := zero_degree_bounded action action ⟨_, hw⟩
  exact ⟨p, congrArg Subtype.val hp, hd⟩
end FiniteControls
end
end Math.PolynomialCovariantEvaluation
