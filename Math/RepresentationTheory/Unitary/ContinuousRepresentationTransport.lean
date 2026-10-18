import Math.RepresentationTheory.Unitary.ContinuousAction
import Math.RepresentationTheory.Unitary.UnitaryRepresentation
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Conjugating a finite-dimensional continuous action by a linear
equivalence preserves joint continuity, with no isometry assumption. -/

set_option autoImplicit false

namespace Math.ContinuousRepresentationTransport

variable {G V W : Type*} [Group G] [TopologicalSpace G]
variable [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

theorem continuous_conjugate (e : V ≃ₗ[ℂ] W) (rho : Representation ℂ G W)
    (h : ContinuousRepresentationScope.IsJointlyContinuous rho) :
    Continuous (fun p : G × V => e.symm (rho p.1 (e p.2))) := by
  have he : Continuous (fun v : V => e v) := e.toLinearMap.continuous_of_finiteDimensional
  have hi : Continuous (fun w : W => e.symm w) :=
    e.symm.toLinearMap.continuous_of_finiteDimensional
  have hp : Continuous (fun p : G × V => (p.1, e p.2)) :=
    continuous_fst.prodMk (he.comp continuous_snd)
  have hr : Continuous (fun p : G × V => rho p.1 (e p.2)) := Continuous.comp h hp
  exact Continuous.comp hi hr

end Math.ContinuousRepresentationTransport
