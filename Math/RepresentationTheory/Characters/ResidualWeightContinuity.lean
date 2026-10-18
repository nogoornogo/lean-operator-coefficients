import Math.RepresentationTheory.Characters.ResidualWeightSpace
import Math.RepresentationTheory.Unitary.ContinuousAction

/-! Residual continuity descends to invariant subspaces and torus weights.
No topology on the torus or ambient gauge group is required. -/

namespace Math.ResidualWeightContinuity

open Representation ResidualWeightSpace ContinuousRepresentationScope

variable {T H V : Type*} [CommGroup T] [Group H] [TopologicalSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem subrepresentation (rho : Representation ℂ (T × H) V)
    (S : Subrepresentation rho) (hr : IsJointlyContinuous (residual rho)) :
    IsJointlyContinuous (residual S.toRepresentation) := by
  rw [IsJointlyContinuous] at hr ⊢
  exact (Continuous.comp hr
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem weight (rho : Representation ℂ (T × H) V)
    (hr : IsJointlyContinuous (residual rho)) (chi : T →* Circle) :
    IsJointlyContinuous (representation rho chi) :=
  hr.subrepresentation (sector rho chi)

end Math.ResidualWeightContinuity
