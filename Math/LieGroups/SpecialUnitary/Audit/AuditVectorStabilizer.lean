import Math.Audit.ImportOrigin
import Math.LieGroups.SpecialUnitary.VectorStabilizer

/-! Actual matrix stabilizers, with rank-zero and non-fixing controls.
No sphere transitivity, local section, or bundle is assumed here. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.Sp).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod then
      throwError "Generic vector stabilizer imports a concrete GUT family: {mod}"

namespace Math.SUN.VectorStabilizer.Audit

noncomputable section

def rotation : Block.Group 2 := ⟨!![0, -1; 1, 0], by
  constructor
  · change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup _ ℂ
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]
  · norm_num [Matrix.det_fin_two]⟩

theorem rotation_not_in_stabilizer : rotation ∉ subgroup 1 := by
  intro h
  have hh := last_column (⟨rotation, h⟩ : subgroup 1) 0
  norm_num [rotation, Fin.last] at hh

theorem rotation_not_in_block : rotation ∉ Set.range (Block.inclusion 1 1) := by
  rintro ⟨g, hg⟩
  exact rotation_not_in_stabilizer (hg ▸ inclusion_mem 1 g)

example : Block.Group 0 ≃ₜ* subgroup 0 := equiv 0
example : Block.Group 5 ≃ₜ* subgroup 5 := equiv 5
example (n : ℕ) (g : Block.Group n) :
    lower (inclusionToStabilizer n g) = g := by
  rw [← equiv_symm_apply, ← equiv_apply, ContinuousMulEquiv.symm_apply_apply]

#print axioms last_column
#print axioms last_row
#print axioms splitMatrix_eq
#print axioms block_unitary
#print axioms block_det
#print axioms inclusion_lower
#print axioms inclusion_mem
#print axioms inclusionToStabilizer_injective
#print axioms inclusionToStabilizer_surjective
#print axioms inclusionToStabilizer_continuous
#print axioms equiv
#print axioms equiv_symm_apply
#print axioms rotation_not_in_stabilizer
#print axioms rotation_not_in_block

end

end Math.SUN.VectorStabilizer.Audit
