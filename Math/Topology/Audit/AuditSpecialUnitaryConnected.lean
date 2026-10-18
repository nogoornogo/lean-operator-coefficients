import Math.Audit.ImportOrigin
import Math.Topology.SpecialUnitaryConnected

/-! The retraction is continuous and surjective, but is not asserted to be
a group homomorphism. Local path-connectedness is not simple-connectedness. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.Sp).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod then
      throwError "Generic SU topology imports a concrete GUT family: {mod}"

namespace Math.SpecialUnitaryTopology.Audit

noncomputable section

def swap : Unitary 2 := ⟨!![0, 1; 1, 0], by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]⟩

theorem retract_not_multiplicative :
    retract 1 (swap * swap) ≠ retract 1 swap * retract 1 swap := by
  have hs : swap * swap = 1 := by
    apply Subtype.ext
    change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, 1; 1, 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hr : (retract 1 swap).val = !![0, -1; 1, 0] := by
    change Matrix.diagonal (fun i : Fin 2 =>
      if i = 0 then star (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ).det else 1) *
        !![0, 1; 1, 0] = !![0, -1; 1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.diagonal_apply]
  have h1 : retract 1 1 = 1 := retract_forget 1 1
  intro h
  rw [hs, h1] at h
  have hh := congrArg (fun g : Special 2 => g.val 0 0) h
  change (1 : ℂ) = ((retract 1 swap).val * (retract 1 swap).val) 0 0 at hh
  rw [hr] at hh
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hh

example : LocallyPathConnectedSpace (Special 0) := locallyPathConnected 0
example : LocallyPathConnectedSpace (Special 1) := locallyPathConnected 1
example : LocallyPathConnectedSpace (Special 5) := locallyPathConnected 5

#print axioms correction_unitary
#print axioms correction_det
#print axioms retract_forget
#print axioms retract_continuous
#print axioms retract_quotient
#print axioms locallyPathConnected
#print axioms retract_not_multiplicative

end

end Math.SpecialUnitaryTopology.Audit
