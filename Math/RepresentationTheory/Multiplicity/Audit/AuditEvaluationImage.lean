import Math.RepresentationTheory.Multiplicity.EvaluationImage
import Math.RepresentationTheory.Decomposition.ExternalTensorDual
import Math.RepresentationTheory.Decomposition.IrreducibilityTransport
import Math.RepresentationTheory.Unitary.SmallSpecialUnitary
import Mathlib.RepresentationTheory.Maschke
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

namespace Math.EvaluationImageAudit
noncomputable section
open Representation MultiplicityEvaluationImage ProductFactorization
open scoped TensorProduct

def scalar := Representation.trivial ℂ Unit ℂ
def ambient (n : ℕ) := Representation.trivial ℂ (Unit × Unit) (Fin n → ℂ)

theorem image_eq_top (n : ℕ) : image (ambient n) scalar = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro v _
  let f : MultiplicitySpace (ambient n) scalar :=
    { toLinearMap := (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight v
      isIntertwining' _ := by ext x; rfl }
  refine ⟨1 ⊗ₜ[ℂ] f, ?_⟩
  change (1 : ℂ) • v = v
  exact one_smul ℂ v

theorem dual_embedding (n : ℕ) :
    ∃ i : IntertwiningMap (model (ambient n) scalar).dual (ambient n).dual,
      Function.Injective i ∧ ∀ phi x,
        i phi (multiplicityEvaluation (ambient n) scalar x) = phi x := by
  let : scalar.IsIrreducible := by
    change (Representation.trivial ℂ Unit ℂ).IsIrreducible
    infer_instance
  exact exists_dual_embedding (ambient n) scalar inferInstance

theorem zero_image : image (ambient 0) scalar = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.eq_bot_of_subsingleton

theorem reducible_image : Module.finrank ℂ (image (ambient 2) scalar).toSubmodule = 2 := by
  rw [image_eq_top]
  change Module.finrank ℂ (⊤ : Submodule ℂ (Fin 2 → ℂ)) = 2
  simp

end
end Math.EvaluationImageAudit

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod || (`Physics).isPrefixOf mod then
      throwError "Evaluation image imports {mod}; original {SourceLayout.originalModule mod}"
  let declarations := [
    ``Math.SemisimpleSplitting.exists_retraction,
    ``Math.RepresentationTheory.isIrreducible_of_comp,
    ``Math.RepresentationTheory.coannihilator,
    ``Math.RepresentationTheory.dual_isIrreducible,
    ``Math.SmallSpecialUnitary.defining_two_irreducible,
    ``Math.SmallSpecialUnitary.defining_three_irreducible,
    ``Math.MultiplicityEvaluationImage.image,
    ``Math.MultiplicityEvaluationImage.toImage,
    ``Math.MultiplicityEvaluationImage.toImage_tmul,
    ``Math.MultiplicityEvaluationImage.toImage_surjective,
    ``Math.MultiplicityEvaluationImage.equiv,
    ``Math.MultiplicityEvaluationImage.equiv_tmul,
    ``Math.MultiplicityEvaluationImage.exists_split,
    ``Math.MultiplicityEvaluationImage.exists_dual_embedding,
    ``Math.MultiplicityEvaluationImage.exists_dual_image,
    ``Math.ExternalTensorDual.equiv,
    ``Math.ExternalTensorDual.rightModelEquiv,
    ``Math.ExternalTensorDual.external_eq,
    ``Math.EvaluationImageAudit.image_eq_top,
    ``Math.EvaluationImageAudit.dual_embedding,
    ``Math.EvaluationImageAudit.zero_image,
    ``Math.EvaluationImageAudit.reducible_image]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Evaluation-image audit: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Evaluation images: {declarations.length} strict axiom checks passed"
