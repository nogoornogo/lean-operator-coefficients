import Math.RepresentationTheory.Multiplicity.ExplicitMultiplicity
import Mathlib.RepresentationTheory.Character

/-! Trace on actual Hilbert multiplicity blocks. The diagonal-entry formula
uses the existing insertions and cyclicity of trace, not a chosen eigenbasis. -/

set_option autoImplicit false

namespace Math.ExplicitMultiplicity

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  (m : I → ℕ) (S : I → Type*)
  [∀ i, NormedAddCommGroup (S i)] [∀ i, InnerProductSpace ℂ (S i)]
  [∀ i, FiniteDimensional ℂ (S i)]

def project (i : I) (a : Fin (m i)) : Space m S →ₗ[ℂ] S i where
  toFun x := x i a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype I] [DecidableEq I] [∀ i, FiniteDimensional ℂ (S i)] in
@[simp] theorem project_apply (i : I) (a : Fin (m i)) (x : Space m S) :
    project m S i a x = x i a := rfl

theorem trace_eq_sum_diagonal (T : Space m S →ₗ[ℂ] Space m S) :
    LinearMap.trace ℂ _ T = ∑ i, ∑ a,
      LinearMap.trace ℂ (S i) ((project m S i a).comp (T.comp (insert m S i a))) := by
  classical
  have he : T = ∑ i, ∑ a, (insert m S i a).comp ((project m S i a).comp T) := by
    apply LinearMap.ext
    intro x
    simpa only [LinearMap.sum_apply, LinearMap.comp_apply, project_apply] using
      (sum_insert m S (T x)).symm
  conv_lhs => rw [he]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [LinearMap.trace_comp_comm']
  rfl

theorem trace_mix_action {G : Type*} [Group G]
    (rho : ∀ i, Representation ℂ G (S i)) (A : Matrices m) (g : G) :
    LinearMap.trace ℂ _ (HilbertMultiplicityOperator.mix m S A * action m S rho g) =
      ∑ i, (A i).trace * (rho i).character g := by
  classical
  rw [trace_eq_sum_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  have he (a : Fin (m i)) :
      (project m S i a).comp
        ((HilbertMultiplicityOperator.mix m S A * action m S rho g).comp (insert m S i a)) =
      A i a a • rho i g := by
    apply LinearMap.ext
    intro x
    change HilbertMultiplicityOperator.mix m S A
      (action m S rho g (insert m S i a x)) i a = _
    rw [action_insert, HilbertMultiplicityOperator.mix_apply]
    simp [insert_apply]
  simp_rw [he, map_smul, smul_eq_mul]
  exact (Finset.sum_mul _ _ _).symm

end

end Math.ExplicitMultiplicity
