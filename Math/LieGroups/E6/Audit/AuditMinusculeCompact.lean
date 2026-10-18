import Math.LieGroups.E6.Minuscule.CompactExponentials
import Math.LieGroups.E6.Minuscule.D5Blocks
import Lean.Util.CollectAxioms

/-!
# E6-0b: bounded matrix prototype, not a compact-group identification

The coordinate spaces and exponentials are actual mathematical objects. The
78-dimensional Lie-basis candidate in `tools/e6` is deliberately not imported
as a theorem, nor is any Spin(10)-to-E6 homomorphism assumed here.
-/

set_option autoImplicit false

namespace Math.E6.Audit

open Minuscule TauCeti.E6Minuscule
open scoped Matrix

example (k : Fin 3) (i : Fin 6) (t : ℝ) :
    NormedSpace.exp (t • compactGenerator k i) ∈
      Matrix.specialUnitaryGroup (Fin 27) ℂ := exp_compactGenerator_mem k i t

example : Module.finrank ℂ (gradeSpace 1) = 16 := gradeSpace_dimensions.1
example : Module.finrank ℂ (gradeSpace (-2)) = 10 := gradeSpace_dimensions.2.1
example : Module.finrank ℂ (gradeSpace 4) = 1 := gradeSpace_dimensions.2.2

example (i : Fin 5) (q : ℤ) (v : Fin 27 → ℂ) (hv : v ∈ gradeSpace q) :
    raising (d5Node i) *ᵥ v ∈ gradeSpace q :=
  (d5_generators_preserve_gradeSpace i q v hv).1

-- Negative controls: E is not self-adjoint, and the omitted E6 root mixes grades.
example : raisingMatrix 0 0 1 = 1 ∧ loweringMatrix 0 0 1 = 0 := by decide +kernel
example : grade 0 = 4 ∧ grade 1 = 1 ∧ raisingMatrix 0 0 1 ≠ 0 := by decide +kernel
example : ¬∀ a : Fin 27, grade a = 0 := by
  intro h
  have : grade 0 = 4 := by decide +kernel
  have hz := h 0
  omega

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.E6.Minuscule.raisingMatrix_transpose,
    ``Math.E6.Minuscule.raising_adjoint,
    ``Math.E6.Minuscule.lowering_adjoint,
    ``Math.E6.Minuscule.cartan_adjoint,
    ``Math.E6.Minuscule.compactX_adjoint,
    ``Math.E6.Minuscule.compactY_adjoint,
    ``Math.E6.Minuscule.compactH_adjoint,
    ``Math.E6.Minuscule.integral_traces,
    ``Math.E6.Minuscule.trace_intCast,
    ``Math.E6.Minuscule.compact_generators_traceless,
    ``Math.E6.Minuscule.compactGenerator_adjoint,
    ``Math.E6.Minuscule.compactGenerator_trace,
    ``Math.E6.Minuscule.exp_compactGenerator_mem,
    ``Math.E6.Minuscule.d5Node_injective,
    ``Math.E6.Minuscule.d5_cartan,
    ``Math.E6.Minuscule.grading_cartan,
    ``Math.E6.Minuscule.grade_values,
    ``Math.E6.Minuscule.grade_cardinalities,
    ``Math.E6.Minuscule.grade_four_iff,
    ``Math.E6.Minuscule.d5_reflection_preserves_grade,
    ``Math.E6.Minuscule.d5_dominant_iff,
    ``Math.E6.Minuscule.d5_dominant_labels,
    ``Math.E6.Minuscule.d5_dominant_grades,
    ``Math.E6.Minuscule.d5_singlet_annihilated,
    ``Math.E6.Minuscule.raisingMatrix_off_block,
    ``Math.E6.Minuscule.loweringMatrix_off_block,
    ``Math.E6.Minuscule.raising_off_block,
    ``Math.E6.Minuscule.lowering_off_block,
    ``Math.E6.Minuscule.cartan_off_block,
    ``Math.E6.Minuscule.gradeSpaceEquiv,
    ``Math.E6.Minuscule.gradeSpace_finrank,
    ``Math.E6.Minuscule.gradeSpace_dimensions,
    ``Math.E6.Minuscule.gradeProjection_mem,
    ``Math.E6.Minuscule.grade_decomposition,
    ``Math.E6.Minuscule.gradeSpace_intersection,
    ``Math.E6.Minuscule.mulVec_mem_gradeSpace,
    ``Math.E6.Minuscule.d5_generators_preserve_gradeSpace,
    ``Math.E6.Minuscule.d5_compact_generators_preserve_gradeSpace]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0b: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0b: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0b: checked {declarations.length} declarations against the standard axiom allowlist"
