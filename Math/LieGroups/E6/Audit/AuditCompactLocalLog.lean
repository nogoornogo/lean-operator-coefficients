import Math.LieGroups.E6.Minuscule.CompactLocalLog
import Math.LieGroups.E6.Audit.AuditCompactNormalizer

/-!
# E6-0i: local real-form logarithm and exponential generation

Positive neighborhood radii are proved to exist, not supplied as hypotheses.
The prior periodic counterexample rejects an unrestricted global converse.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule NormedSpace Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

example : ∀ᶠ g : compactNormalizer in 𝓝 1,
    compactLocalLog g ∈ compactMatrixLieAlgebra := eventually_compactLocalLog_mem

example : ∃ ε > (0 : ℝ), ∀ X : Matrix27, ‖X‖ < ε →
    (exp X ∈ compactNormalizerMatrices ↔ X ∈ compactMatrixLieAlgebra) :=
  exists_exp_criterion_radius

example : ∃ ε > (0 : ℝ), ∀ g : compactNormalizer, dist g 1 < ε →
    compactLocalLog g ∈ compactMatrixLieAlgebra ∧
      exp (compactLocalLog g) = (g.val : Matrix27) := exists_localLog_radius

example : IsOpen (compactIdentityComponent : Set compactNormalizer) :=
  compactIdentityComponent_isOpen

example : compactExponentialSubgroup = compactIdentityComponent :=
  compactExponentialSubgroup_eq_identityComponent

example : compactLocalLog 1 = 0 := MatrixLieGroupNormalizer.localLog_one _

theorem no_global_exp_converse :
    ¬∀ X : Matrix27, exp X ∈ compactNormalizerMatrices → X ∈ compactMatrixLieAlgebra := by
  intro h
  obtain ⟨X, he, hn⟩ := single_exponential_not_sufficient
  exact hn (h X he)

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.LieNormalizerLocalLog.log_one_add_apply_mem,
    ``Math.LieNormalizerLocalLog.eventually_invariant_of_exp_invariant,
    ``Math.LieNormalizerLocalLog.eventually_normalizes_of_exp_conjugate_mem,
    ``Math.SpecialUnitaryLocalLog.exp_star_eq_exp_neg_of_unitary,
    ``Math.SpecialUnitaryLocalLog.eventually_skew_of_exp_unitary,
    ``Math.SpecialUnitaryLocalLog.eventually_trace_zero_of_exp_special,
    ``Math.SpecialUnitaryLocalLog.eventually_exp_mem_iff,
    ``Math.MatrixLieGroupNormalizer.eventually_exp_mem_matrixCarrier_iff,
    ``Math.MatrixLieGroupNormalizer.localLog_one,
    ``Math.MatrixLieGroupNormalizer.localLog_tendsto,
    ``Math.MatrixLieGroupNormalizer.eventually_exp_localLog,
    ``Math.MatrixLieGroupNormalizer.eventually_localLog_conditions,
    ``Math.E6.Minuscule.eventually_exp_mem_normalizer_iff,
    ``Math.E6.Minuscule.eventually_compactLocalLog_mem,
    ``Math.E6.Minuscule.eventually_exp_compactLocalLog,
    ``Math.E6.Minuscule.eventually_local_realForm_exp,
    ``Math.E6.Minuscule.mem_identityComponent_of_realForm_exp,
    ``Math.E6.Minuscule.eventually_mem_compactIdentityComponent,
    ``Math.E6.Minuscule.compactIdentityComponent_isOpen,
    ``Math.E6.Minuscule.exists_exp_criterion_radius,
    ``Math.E6.Minuscule.exists_localLog_radius,
    ``Math.E6.Minuscule.compactExponentialSubgroup_le,
    ``Math.E6.Minuscule.compactExponentialSubgroup_isOpen,
    ``Math.E6.Minuscule.compactExponentialSubgroup_eq_identityComponent,
    ``Math.E6.Audit.no_global_exp_converse]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0i: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0i: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0i: checked {declarations.length} declarations against the standard axiom allowlist"
