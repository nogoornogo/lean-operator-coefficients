import Math.Audit.ImportOrigin
import Math.Topology.SimplyConnectedUnion
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Positive gluing and an empty-overlap control. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SUN).isPrefixOf mod || (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.Sp).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod then
      throwError "General gluing imports a concrete group family: {mod}"

namespace Math.SimplyConnectedUnion.Audit

theorem real_two_open_sets : SimplyConnectedSpace ℝ := by
  have hu : IsSimplyConnected (Set.Iio (1 : ℝ)) := by
    let := (convex_Iio (1 : ℝ)).contractibleSpace ⟨0, by norm_num⟩
    exact inferInstanceAs (SimplyConnectedSpace (Set.Iio (1 : ℝ)))
  have hv : IsSimplyConnected (Set.Ioi (0 : ℝ)) := by
    let := (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩
    exact inferInstanceAs (SimplyConnectedSpace (Set.Ioi (0 : ℝ)))
  apply simplyConnected_of_open_cover isOpen_Iio isOpen_Ioi hu hv
  · exact ((convex_Iio (𝕜 := ℝ) (1 : ℝ)).inter (convex_Ioi (0 : ℝ))).isPathConnected
      ⟨1 / 2, by norm_num⟩
  · ext x
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_univ, iff_true]
    rcases lt_or_ge x 1 with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)

section DisjointControl

local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩

theorem singletons_simplyConnected :
    IsSimplyConnected ({true} : Set Bool) ∧ IsSimplyConnected ({false} : Set Bool) := by
  exact ⟨inferInstanceAs (SimplyConnectedSpace ({true} : Set Bool)),
    inferInstanceAs (SimplyConnectedSpace ({false} : Set Bool))⟩

theorem disjoint_cover : ({true} : Set Bool) ∪ {false} = Set.univ := by
  ext b
  cases b <;> simp

theorem disjoint_overlap_not_pathConnected :
    ¬ IsPathConnected (({true} : Set Bool) ∩ {false}) := by
  intro h
  obtain ⟨b, hb⟩ := h.nonempty
  simp at hb

theorem disjoint_union_not_simplyConnected : ¬ SimplyConnectedSpace Bool := by
  intro h
  let := h
  have hs : Subsingleton Bool := subsingleton_of_preconnected_totallyDisconnected
  exact Bool.noConfusion (hs.elim true false)

end DisjointControl

#print axioms homotopic_of_mem
#print axioms transport_of_open_cover
#print axioms simplyConnected_of_open_cover
#print axioms real_two_open_sets
#print axioms singletons_simplyConnected
#print axioms disjoint_union_not_simplyConnected

end Math.SimplyConnectedUnion.Audit
