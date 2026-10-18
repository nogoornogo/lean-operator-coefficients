import Math.LieGroups.Spin.SU5LiftPreparation
import Math.LieGroups.SpecialUnitary.SimplyConnected

/-! The actual continuous injective SU(5) inclusion in compact real Spin(10).
Both source topology requirements are proved, not additional premises. -/

set_option autoImplicit false

namespace Math.CompactSpin

noncomputable section

theorem SU5_simplyConnected : SimplyConnectedSpace SU5 :=
  SUN.SphereSection.specialUnitary_simplyConnected 5

theorem exists_SU5_inclusion :
    ∃ i : SU5 →* Group 10, Continuous i ∧ Function.Injective i ∧
      (projection 10).comp i = realification := by
  let := SU5_simplyConnected
  exact exists_SU5_inclusion_of_simplyConnected

def SU5Inclusion : SU5 →* Group 10 := exists_SU5_inclusion.choose

theorem SU5Inclusion_continuous : Continuous SU5Inclusion :=
  exists_SU5_inclusion.choose_spec.1

theorem SU5Inclusion_injective : Function.Injective SU5Inclusion :=
  exists_SU5_inclusion.choose_spec.2.1

theorem projection_comp_SU5Inclusion : (projection 10).comp SU5Inclusion = realification :=
  exists_SU5_inclusion.choose_spec.2.2

theorem SU5Inclusion_isClosedEmbedding : Topology.IsClosedEmbedding SU5Inclusion :=
  SU5Inclusion_continuous.isClosedEmbedding SU5Inclusion_injective

def continuousSU5Inclusion : SU5 →ₜ* Group 10 where
  toMonoidHom := SU5Inclusion
  continuous_toFun := SU5Inclusion_continuous

/-- The choice of the based continuous homomorphic lift cannot change the inclusion. -/
theorem SU5Inclusion_unique (i : SU5 →* Group 10) (hi : Continuous i)
    (hp : (projection 10).comp i = realification) : i = SU5Inclusion := by
  let := SU5_simplyConnected
  let := SU5_locallyPathConnected
  exact (existsUnique_lift 10 realification realification_continuous).unique
    ⟨hi, hp⟩ ⟨SU5Inclusion_continuous, projection_comp_SU5Inclusion⟩

end

end Math.CompactSpin
