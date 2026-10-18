import TauCeti.Topology.Algebra.Module.FiniteDimension
import Math.RepresentationTheory.Unitary.ContinuousConstructions
import TauCeti.RepresentationTheory.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-! Exterior actions on a finite-dimensional analytic copy are continuous
when the original action has continuous orbits. -/
namespace Math.ExteriorContinuity
set_option autoImplicit false
noncomputable section
open Representation
variable {G V W : Type*} [Group G] [TopologicalSpace G]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W]

theorem continuous_orbit [NormedSpace ℂ W] (rho : Representation ℂ G V)
    (hr : ∀ v, Continuous (fun g => rho g v)) (n : ℕ)
    (e : (⋀[ℂ]^n V) ≃ₗ[ℂ] W) (x : ⋀[ℂ]^n V) :
    Continuous (fun g => e (rho.exteriorPower n g x)) := by
  have hx : x ∈ Submodule.span ℂ (Set.range (exteriorPower.ιMulti ℂ n)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    let q := e.toLinearMap.compMultilinearMap (exteriorPower.ιMulti ℂ n).toMultilinearMap
    have hq : Continuous q := q.continuous_of_finiteDimensional
    have he : (fun g => e (rho.exteriorPower n g (exteriorPower.ιMulti ℂ n v))) =
        fun g => q (fun i => rho g (v i)) := by
      funext g
      rw [Representation.exteriorPower_apply_ιMulti]
      rfl
    rw [he]
    exact hq.comp (continuous_pi (fun i => hr (v i)))
  | zero => simpa using (continuous_const : Continuous (fun _ : G => (0 : W)))
  | add x y _ _ hx hy =>
    convert hx.add hy using 1
    funext g
    simp
  | smul c x _ hx =>
    convert hx.const_smul c using 1
    funext g
    simp

theorem representation_continuous [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (rho : Representation ℂ G V) (hr : ∀ v, Continuous (fun g => rho g v))
    (n : ℕ) (sigma : Representation ℂ G W)
    (e : Representation.Equiv (rho.exteriorPower n) sigma) :
    ContinuousRepresentationScope.IsJointlyContinuous sigma := by
  apply ContinuousUnitaryConstructions.jointlyContinuous_of_orbit
  intro x
  obtain ⟨y,rfl⟩ := e.surjective x
  exact (continuous_orbit rho hr n e.toLinearEquiv y).congr
    (fun g => e.isIntertwining _ _ g y)

end
end Math.ExteriorContinuity
