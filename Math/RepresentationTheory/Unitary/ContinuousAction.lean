import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

/-! # Jointly continuous finite-dimensional representations -/

namespace Math.ContinuousRepresentationScope
noncomputable section

variable {G H V : Type*}
variable [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

/-- The action map `(g,v) |-> rho(g)v` is jointly continuous. -/
def IsJointlyContinuous (rho : Representation ℂ G V) : Prop :=
  Continuous fun p : G × V => rho p.1 p.2

theorem IsJointlyContinuous.orbit
    {rho : Representation ℂ G V} (h : IsJointlyContinuous rho) (v : V) :
    Continuous fun g => rho g v := by
  exact h.comp (continuous_id.prodMk continuous_const)

theorem IsJointlyContinuous.operator
    {rho : Representation ℂ G V} (h : IsJointlyContinuous rho) (g : G) :
    Continuous fun v => rho g v := by
  exact h.comp (continuous_const.prodMk continuous_id)

/-- An invariant subspace, with its subtype topology, inherits joint
continuity from the ambient representation. -/
theorem IsJointlyContinuous.subrepresentation
    {rho : Representation ℂ G V} (h : IsJointlyContinuous rho)
    (S : Subrepresentation rho) :
    IsJointlyContinuous S.toRepresentation := by
  rw [IsJointlyContinuous] at h ⊢
  apply continuous_induced_rng.mpr
  exact h.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

variable [Group H] [TopologicalSpace H]

/-- Joint continuity is preserved by restriction along a continuous group
homomorphism. -/
theorem IsJointlyContinuous.comp
    {rho : Representation ℂ G V} (h : IsJointlyContinuous rho)
    (phi : H →ₜ* G) :
    IsJointlyContinuous (rho.comp (phi : H →* G)) := by
  exact Continuous.comp h
    ((phi.continuous.comp continuous_fst).prodMk continuous_snd)

/-- The exact scope in which the project invokes compact Lie-group highest
weight classification. -/
structure IsContinuousFiniteDimensionalIrrep
    (rho : Representation ℂ G V) : Prop where
  finiteDimensional : FiniteDimensional ℂ V
  irreducible : Representation.IsIrreducible rho
  continuous_action : IsJointlyContinuous rho

end
end Math.ContinuousRepresentationScope
