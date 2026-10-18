import Math.Audit.ImportOrigin
import Math.LieGroups.SpecialUnitary.SimplyConnected

/-! Actual SU topology, from base ranks through the induction used by the Spin lift. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.Sp).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod then
      throwError "SU topology imports a fixed gauge family: {mod}"

namespace Math.SUN.SphereSection.Audit

example : SimplyConnectedSpace (Block.Group 0) := specialUnitary_simplyConnected 0
example : SimplyConnectedSpace (Block.Group 1) := specialUnitary_simplyConnected 1
example : SimplyConnectedSpace (Block.Group 2) := specialUnitary_simplyConnected 2
example : SimplyConnectedSpace (Block.Group 5) := specialUnitary_simplyConnected 5

theorem two_poles_distinct (n : ℕ) : north n ≠ antipode (north n) := by
  intro h
  have hh := congrArg (fun v : Sphere (n + 1) => v.val (Fin.last n)) h
  norm_num [north, antipode] at hh

example : IsPathConnected (patch 1 ∩ southPatch 1) := overlap_pathConnected 0
example : IsPathConnected (projection ⁻¹' (patch 4 ∩ southPatch 4)) := by
  let := specialUnitary_pathConnected 4
  exact overlapPreimage_pathConnected 3

#print axioms Math.PuncturedSphere.stereo_image_compl_zero
#print axioms Math.PuncturedSphere.isPathConnected_compl_antipodes
#print axioms Block.rank_one_eq_one
#print axioms Block.rank_one_simplyConnected
#print axioms Block.rank_zero_simplyConnected
#print axioms denominator_eq_zero_iff
#print axioms patch_contractible
#print axioms southPatch_contractible
#print axioms patchProductHomotopyEquiv
#print axioms southProductHomotopyEquiv
#print axioms northPreimage_simplyConnected
#print axioms southPreimage_simplyConnected
#print axioms overlap_pathConnected
#print axioms overlapLocalProduct
#print axioms overlapPreimage_pathConnected
#print axioms specialUnitary_pathConnected
#print axioms simplyConnected_succ
#print axioms specialUnitary_simplyConnected
#print axioms two_poles_distinct

end Math.SUN.SphereSection.Audit
