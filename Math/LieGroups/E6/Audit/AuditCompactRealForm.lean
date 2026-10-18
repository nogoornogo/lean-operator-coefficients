import Math.LieGroups.E6.Minuscule.CompactRealForm
import Lean.Util.CollectAxioms

/-!
# E6-0e: actual real forms, complexification, and compatible D5 inclusion

No real-form certificate, dimension, or integration hypothesis is supplied.
Global group identification and the compact Spin inclusion remain separate.
-/

set_option autoImplicit false

namespace Math.E6.Audit

noncomputable section

open Minuscule TauCeti.DynkinType TauCeti.E6Minuscule
open scoped Matrix TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing

example : Module.finrank ℝ compactRealForm = 78 := compactRealForm_finrank
example : Module.finrank ℝ d5CompactRealForm = 45 := d5CompactRealForm_finrank
example : ℂ ⊗[ℝ] compactRealForm ≃ₗ⁅ℂ⁆ E6.lieAlgebraBaseChange valid_E6 ℂ :=
  compactGeckEquiv
example : ℂ ⊗[ℝ] d5CompactRealForm ≃ₗ⁅ℂ⁆ (D 5).lieAlgebraBaseChange valid_D5 ℂ :=
  d5CompactGeckEquiv
example : Function.Injective compactD5Inclusion := compactD5Inclusion_injective

example (z : ℂ ⊗[ℝ] d5CompactRealForm) :
    compactGeckEquiv (LieAlgebra.ExtendScalars.map (AlgHom.id ℝ ℂ) compactD5Inclusion z) =
      geckD5Inclusion ℂ (d5CompactGeckEquiv z) := compactGeckEquiv_inclusion z

example (x : compactRealForm) (t : ℝ) :
    NormedSpace.exp (t • x.val.val) ∈ Matrix.specialUnitaryGroup (Fin 27) ℂ :=
  exp_compactRealForm_mem x t

example (x : d5CompactRealForm) (t : ℝ) :
    NormedSpace.exp (t • x.val.val) ∈ Matrix.specialUnitaryGroup (Fin 27) ℂ :=
  exp_compactRealForm_mem (compactD5Inclusion x) t

example (x y : compactRealForm) :
    (⁅x, y⁆).val.val = ⁅x.val.val, y.val.val⁆ := rfl

-- A complex root vector is not in the real form: the fixed-point condition
-- is a genuine restriction, not all of the 156-dimensional real carrier.
theorem raising_zero_not_skew : (raising 0)ᴴ ≠ -raising 0 := by
  intro h
  rw [raising_adjoint] at h
  have he : raisingMatrix 0 0 1 = 1 := by decide +kernel
  have hf : loweringMatrix 0 0 1 = 0 := by decide +kernel
  have hab := congrArg (fun M : Matrix27 => M 0 1) h
  change (loweringMatrix 0 0 1 : ℂ) = -(raisingMatrix 0 0 1 : ℂ) at hab
  rw [he, hf] at hab
  norm_num at hab

example : (⟨raising 0, raising_mem_matrixLieAlgebra 0⟩ : matrixLieAlgebra ℂ) ∉
    compactRealForm := by
  rw [MatrixCompactRealForm.mem_realForm]
  exact raising_zero_not_skew

example : (compactGeneratorElement 0 0).val.val ≠ 0 := by
  intro h
  have he : raisingMatrix 0 0 1 = 1 := by decide +kernel
  have hf : loweringMatrix 0 0 1 = 0 := by decide +kernel
  have hab := congrArg (fun M : Matrix27 => M 0 1) h
  change (raisingMatrix 0 0 1 : ℂ) - (loweringMatrix 0 0 1 : ℂ) = 0 at hab
  rw [he, hf] at hab
  norm_num at hab

end

end Math.E6.Audit

run_cmd do
  let declarations := [
    ``Math.MatrixCompactRealForm.adjoint_lie,
    ``Math.MatrixCompactRealForm.adjoint_mem_lieSpan,
    ``Math.MatrixCompactRealForm.conjugation,
    ``Math.MatrixCompactRealForm.conjugation_involutive,
    ``Math.MatrixCompactRealForm.conjugation_lie,
    ``Math.MatrixCompactRealForm.realForm,
    ``Math.MatrixCompactRealForm.mem_realForm,
    ``Math.MatrixCompactRealForm.complexification,
    ``Math.MatrixCompactRealForm.complexification_tmul,
    ``Math.MatrixCompactRealForm.finrank_realForm,
    ``Math.MatrixCompactRealForm.representation,
    ``Math.MatrixCompactRealForm.representation_injective,
    ``Math.MatrixCompactRealForm.representation_adjoint,
    ``Math.MatrixCompactRealForm.inclusion,
    ``Math.MatrixCompactRealForm.inclusion_injective,
    ``Math.E6.Minuscule.matrixLieAlgebra_adjoint,
    ``Math.E6.Minuscule.d5MatrixLieAlgebra_adjoint,
    ``Math.E6.Minuscule.compactRealForm_finrank,
    ``Math.E6.Minuscule.d5CompactRealForm_finrank,
    ``Math.E6.Minuscule.compactGeckEquiv,
    ``Math.E6.Minuscule.d5CompactGeckEquiv,
    ``Math.E6.Minuscule.compactD5Inclusion,
    ``Math.E6.Minuscule.compactD5Inclusion_injective,
    ``Math.E6.Minuscule.compactGeckEquiv_inclusion,
    ``Math.E6.Minuscule.raising_mem_matrixLieAlgebra,
    ``Math.E6.Minuscule.lowering_mem_matrixLieAlgebra,
    ``Math.E6.Minuscule.cartan_mem_matrixLieAlgebra,
    ``Math.E6.Minuscule.compactGenerator_mem_matrixLieAlgebra,
    ``Math.E6.Minuscule.compactGeneratorElement,
    ``Math.E6.Minuscule.matrixLieAlgebra_trace,
    ``Math.E6.Minuscule.exp_compactRealForm_mem,
    ``Math.E6.Audit.raising_zero_not_skew]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "E6-0e: {decl} uses unexpected axiom {ax}"
    Lean.logInfo m!"E6-0e: {decl} depends on axioms: {axioms}"
  Lean.logInfo m!"E6-0e: checked {declarations.length} declarations against the standard axiom allowlist"
