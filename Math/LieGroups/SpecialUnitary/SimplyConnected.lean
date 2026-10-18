import Math.LieGroups.SpecialUnitary.SpherePatchTopology
import Math.Topology.SimplyConnectedUnion

/-! Simple-connectedness of every actual complex special unitary matrix group.
The induction glues two open sphere charts with path-connected overlap. -/

set_option autoImplicit false

namespace Math.SUN.SphereSection

theorem simplyConnected_succ (n : ℕ) [SimplyConnectedSpace (Block.Group (n + 1))] :
    SimplyConnectedSpace (Block.Group (n + 2)) := by
  apply Math.SimplyConnectedUnion.simplyConnected_of_open_cover
    ((patch_isOpen (n + 1)).preimage (projection_continuous (n + 1)))
    ((southPatch_isOpen (n + 1)).preimage (projection_continuous (n + 1)))
    (northPreimage_simplyConnected n) (southPreimage_simplyConnected n)
    (overlapPreimage_pathConnected n) (preimages_union_univ n)

theorem specialUnitary_simplyConnected (n : ℕ) : SimplyConnectedSpace (Block.Group n) := by
  cases n with
  | zero => exact Block.rank_zero_simplyConnected
  | succ n =>
    induction n with
    | zero => exact Block.rank_one_simplyConnected
    | succ n ih =>
      let := ih
      exact simplyConnected_succ n

end Math.SUN.SphereSection
