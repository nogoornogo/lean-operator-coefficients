import Math.RepresentationTheory.Constructions.FiniteGroupPolynomialEvaluation

/-! Controls for a nontrivial finite permutation action and its exceptional zero orbit. -/
namespace Math.PolynomialCovariantEvaluation.FiniteControls
noncomputable section
open Representation

abbrev H := Equiv.Perm (Fin 2)
abbrev V := Fin 2 → ℂ

def action : Representation ℂ H V where
  toFun g := {
    toFun x i := x (g⁻¹ i)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  map_one' := rfl
  map_mul' _ _ := rfl

def value : V := fun i => (i.val : ℂ)

theorem value_injective : Function.Injective value := by
  intro i j h
  apply Fin.ext
  change (i.val : ℂ) = (j.val : ℂ) at h
  exact_mod_cast h

/-- This chosen value has trivial stabilizer, although its group action is nontrivial. -/
theorem value_stabilizer (g : H) (hg : g ∈ stabilizer action value) : g = 1 := by
  change (fun i => value (g⁻¹ i)) = value at hg
  have hi : ∀ i, g⁻¹ i = i := fun i => value_injective (congrFun hg i)
  have hgi : g⁻¹ = 1 := Equiv.ext hi
  exact inv_eq_one.mp hgi

/-- At this value any target vector, including a noninvariant one, is attained. -/
theorem free_value_evaluation (w : V) :
    ∃ p : covariants action action, evaluate value p.val = w := by
  have hw : w ∈ Representation.invariants (action.comp (stabilizer action value).subtype) := by
    intro g
    change action g.val w = w
    rw [value_stabilizer g.val g.property]
    simp
  obtain ⟨p, hp⟩ := finite_group_surjective action action value ⟨w, hw⟩
  exact ⟨p, congrArg Subtype.val hp⟩

/-- The zero orbit has full stabilizer; evaluations must have equal coordinates. -/
theorem zero_evaluation_equal (p : covariants action action) :
    evaluate (0 : V) p.val 0 = evaluate (0 : V) p.val 1 := by
  have h := p.property (Equiv.swap (0 : Fin 2) 1) 0
  have h0 := congrFun h 0
  simpa [action] using h0

/-- The noninvariant chosen vector is attained at the free value. -/
theorem free_attains_value : ∃ p : covariants action action,
    evaluate value p.val = value := free_value_evaluation value

/-- At zero, the invariant constant vector is still attained. -/
theorem zero_attains_constant : ∃ p : covariants action action,
    evaluate (0 : V) p.val = (fun _ => 1) := by
  have hw : (fun _ : Fin 2 => (1 : ℂ)) ∈
      Representation.invariants (action.comp (stabilizer action (0 : V)).subtype) := by
    intro g
    rfl
  obtain ⟨p, hp⟩ := finite_group_surjective action action (0 : V) ⟨_, hw⟩
  exact ⟨p, congrArg Subtype.val hp⟩

/-- The same vector cannot be attained at zero: ambient saturation would be false. -/
theorem zero_not_attains_value : ¬ ∃ p : covariants action action,
    evaluate (0 : V) p.val = value := by
  rintro ⟨p, hp⟩
  have h := zero_evaluation_equal p
  rw [hp] at h
  norm_num [value] at h
end
end Math.PolynomialCovariantEvaluation.FiniteControls
