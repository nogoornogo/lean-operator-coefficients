import Math.RepresentationTheory.Jets.JetEquationComparison
import Math.Algebra.Jets.ScalarJetQuadratic

/-! Complete one-dimensional quadratic EOM/IBP quotient, derived from all
descendants of the actual equation φ''=0 on the unbounded jet tower. -/
namespace Math.ScalarJetEOMQuadratic
set_option autoImplicit false
noncomputable section
open MvPolynomial ScalarJetQuadratic

def equation : JetDirections.Symbols Unit := X () ^ 2

theorem higher_relation (k : ℕ) :
    Finsupp.single (jetIndex (k + 2)) (1 : ℂ) ∈ JetEquation.relations Unit equation := by
  have h := JetEquation.descendant_mem equation () (X () ^ k)
  have he : X () ^ k * equation = monomial (Finsupp.single () (k + 2)) (1 : ℂ) := by
    rw [equation, ← pow_add, X_pow_eq_monomial]
  rw [he, JetDirections.ofSymbols_monomial] at h
  exact h

theorem higher_projection (k : ℕ) : JetEquation.projection equation (X (jetIndex (k + 2))) = 0 := by
  rw [JetEquation.projection_X, show (JetEquation.relations Unit equation).mkQ
    (Finsupp.single (jetIndex (k + 2)) 1) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr (higher_relation k), map_zero]

theorem second_eom : second ∈ (JetEquation.gradeProjection equation 2 2).ker := by
  apply (JetEquation.eom_kernel_iff equation 2 2 second).mpr
  rw [← JetEquation.projection_ker]
  change JetEquation.projection equation (monomial secondExponent 1) = 0
  rw [secondExponent, MvPolynomial.monomial_add_single]
  simp only [pow_one, map_mul]
  rw [higher_projection 0, mul_zero]

theorem combinedRelations_top : JetEquation.combinedRelations (S := Unit) equation 2 1 = ⊤ := by
  let R := JetEquation.combinedRelations (S := Unit) equation 2 1
  have hs : second ∈ R := (show (JetEquation.gradeProjection equation 2 2).ker ≤ R from le_sup_left) second_eom
  have hsum : first + second ∈ R := by
    apply (show JetEquation.offRelations (S := Unit) (I := Unit) 2 1 ≤ R from le_sup_right)
    rw [← derivative_primitive]
    exact GradedJetIBP.derivative_mem (JetEquation.offDerivatives 2) 1 () primitive
  have hf : first ∈ R := by simpa using R.sub_mem hsum hs
  apply top_unique
  intro p _
  rw [source_reconstruct p]
  exact R.add_mem (R.smul_mem _ hf) (R.smul_mem _ hs)

abbrev CombinedQuotient := Source ⧸ JetEquation.combinedRelations (S := Unit) equation 2 1
abbrev ShellQuotient := JetEquation.grade Unit equation 2 2 ⧸ JetEquation.shellRelations equation 2 1

theorem combined_zero (p : CombinedQuotient) : p = 0 := by
  obtain ⟨p, rfl⟩ := (JetEquation.combinedRelations (S := Unit) equation 2 1).mkQ_surjective p
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [combinedRelations_top]
  trivial

theorem shell_zero (p : ShellQuotient) : p = 0 := by
  obtain ⟨p, rfl⟩ := (JetEquation.combinedQuotientEquiv (S := Unit) equation 2 1).surjective p
  rw [combined_zero p, map_zero]

theorem shell_finrank : Module.finrank ℂ ShellQuotient = 0 := by
  have : Subsingleton ShellQuotient := ⟨fun a b => (shell_zero a).trans (shell_zero b).symm⟩
  exact Module.finrank_zero_of_subsingleton

end
end Math.ScalarJetEOMQuadratic
