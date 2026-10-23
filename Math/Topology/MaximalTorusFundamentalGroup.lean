import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# External maximal-torus fundamental-group theorem interface

`MaximalTorusSurjectivityInput` is a proposition, not an instance or an axiom.
It records the surjectivity part of Raghunathan, Proposition 38, for a compact
connected finite-dimensional real Lie group. Its proof is deliberately an
explicit external input. No claim that this literature theorem is formalized
is made here. See `docs/proof/E6_LITERATURE_BOUNDARY.md`.

The torus data use maximality among Abelian subgroups, a sufficient (stronger)
condition for maximality among tori. Normality of the torus is not required.
-/

set_option autoImplicit false

namespace Math.Topology

open scoped Manifold ContDiff

/-- A closed embedded finite torus, maximal among Abelian subgroups. -/
structure MaximalTorusData (G : Type*) [Group G] [TopologicalSpace G] where
  rank : ℕ
  hom : (Fin rank → Circle) →* G
  continuous : Continuous hom
  closedEmbedding : Topology.IsClosedEmbedding hom
  maximal : ∀ A : Subgroup G, hom.range ≤ A →
    (∀ a ∈ A, ∀ b ∈ A, Commute a b) → A = hom.range

namespace MaximalTorusData

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- The actual based map induced by the given inclusion, not an arbitrary map. -/
noncomputable def fundamentalMap (T : MaximalTorusData G) :
    FundamentalGroup (Fin T.rank → Circle) 1 →* FundamentalGroup G 1 :=
  FundamentalGroup.mapOfEq ⟨T.hom, T.continuous⟩ (map_one T.hom)

end MaximalTorusData

/-- EXTERNAL INPUT, not a proved theorem: maximal-torus inclusion is surjective
on fundamental groups. All geometric hypotheses are part of this interface. -/
def MaximalTorusSurjectivityInput
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : Type*) [Group G] [TopologicalSpace G] [T2Space G]
    [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G]
    [CompactSpace G] [ConnectedSpace G] : Prop :=
  ∀ T : MaximalTorusData G, Function.Surjective T.fundamentalMap

/-- Basepoint transport closes the elementary consumer without assuming
that the domain of the surjective fundamental-group map is simply connected. -/
theorem simplyConnected_of_pi1_eq_one {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] (x₀ : X)
    (h : ∀ c : FundamentalGroup X x₀, c = 1) : SimplyConnectedSpace X := by
  refine simply_connected_iff_loops_nullhomotopic.mpr ⟨inferInstance, ?_⟩
  intro x p
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x x₀
  have he : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p) = 1 :=
    e.injective ((h _).trans (map_one e).symm)
  have hp := congrArg FundamentalGroup.toPath he
  exact Quotient.eq.mp hp

end Math.Topology
