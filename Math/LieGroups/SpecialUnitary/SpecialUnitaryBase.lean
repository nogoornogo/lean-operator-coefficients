import Math.LieGroups.SpecialUnitary.Block
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The actual empty and one-dimensional special unitary groups are points. -/

set_option autoImplicit false

namespace Math.SUN.Block

theorem rank_one_eq_one (g : Group 1) : g = 1 := by
  apply Subtype.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  have hd := g.property.2
  change Matrix.det g.val = 1 at hd
  simpa [Matrix.det_fin_one] using hd

theorem rank_one_subsingleton : Subsingleton (Group 1) :=
  ⟨fun g h => (rank_one_eq_one g).trans (rank_one_eq_one h).symm⟩

theorem rank_one_simplyConnected : SimplyConnectedSpace (Group 1) := by
  let := rank_one_subsingleton
  infer_instance

theorem rank_zero_simplyConnected : SimplyConnectedSpace (Group 0) := by
  infer_instance

end Math.SUN.Block
