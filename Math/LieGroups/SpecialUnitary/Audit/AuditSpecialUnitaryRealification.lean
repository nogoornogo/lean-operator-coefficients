import Math.Audit.ImportOrigin
import Math.LieGroups.SpecialUnitary.SpecialUnitaryRealification

/-! Real-coordinate orientation, an actual nontrivial matrix, and boundary ranks. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod ||
        (`GUT.Spin).isPrefixOf mod then
      throwError "Generic realification imports a concrete GUT family: {mod}"

namespace Math.SpecialUnitaryRealification.Audit

noncomputable section

theorem real_imaginary_order : coordinates 1 ![2, 3] 0 = 2 + 3 * Complex.I := by
  change (⟨2, 3⟩ : ℂ) = 2 + 3 * Complex.I
  apply Complex.ext <;> norm_num

def minusTwo : Source 2 := by
  refine ⟨-1, ?_, ?_⟩
  · change star (-1 : Matrix (Fin 2) (Fin 2) ℂ) * (-1) = 1 ∧
      (-1 : Matrix (Fin 2) (Fin 2) ℂ) * star (-1) = 1
    constructor <;> simp
  · change Matrix.det (-1 : Matrix (Fin 2) (Fin 2) ℂ) = 1
    norm_num [Matrix.det_fin_two]

theorem minusTwo_ne_one : minusTwo ≠ 1 := by
  intro h
  have hh := congrArg (fun g : Source 2 => g.val 0 0) h
  norm_num [minusTwo] at hh

theorem realification_nontrivial : hom 2 minusTwo ≠ 1 := by
  intro h
  apply minusTwo_ne_one
  exact hom_injective 2 (h.trans (map_one (hom 2)).symm)

example : Function.Injective (hom 0) := hom_injective 0
example : Function.Injective (hom 1) := hom_injective 1
example : Topology.IsClosedEmbedding (hom 5) := hom_isClosedEmbedding 5

#print axioms form_coordinates
#print axioms preserves_form
#print axioms realAction_det
#print axioms hom
#print axioms hom_injective
#print axioms hom_continuous
#print axioms hom_isClosedEmbedding
#print axioms real_imaginary_order
#print axioms realification_nontrivial

end

end Math.SpecialUnitaryRealification.Audit
