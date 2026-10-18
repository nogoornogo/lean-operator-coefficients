import Math.LieGroups.Spin.CoveringLift
import Math.LieGroups.SpecialUnitary.SpecialUnitaryRealification
import Math.Topology.SpecialUnitaryConnected

/-! The concrete SU(5) -> SO(10) leg of the standard Spin chain.
Local path-connectedness and the topology-conditional lift interfaces are proved here.
`SU5Inclusion` closes the simple-connectedness premise and constructs the inclusion. -/

set_option autoImplicit false

namespace Math.CompactSpin

noncomputable section

abbrev SU5 := SpecialUnitaryRealification.Source 5

def realification : SU5 →* Orthogonal 10 := SpecialUnitaryRealification.hom 5

theorem realification_continuous : Continuous realification :=
  SpecialUnitaryRealification.hom_continuous 5

theorem realification_injective : Function.Injective realification :=
  SpecialUnitaryRealification.hom_injective 5

theorem realification_isClosedEmbedding : Topology.IsClosedEmbedding realification :=
  SpecialUnitaryRealification.hom_isClosedEmbedding 5

/-- Original topology-conditional interface, retained for compatibility. -/
theorem exists_SU5_inclusion_of_topology
    [SimplyConnectedSpace SU5] [LocallyPathConnectedSpace SU5] :
    ∃ i : SU5 →* Group 10, Continuous i ∧ Function.Injective i ∧
      (projection 10).comp i = realification :=
  exists_injective_lift 10 realification realification_continuous realification_injective

theorem SU5_locallyPathConnected : LocallyPathConnectedSpace SU5 :=
  SpecialUnitaryTopology.locallyPathConnected 5

/-- Compatibility interface with an explicit simple-connectedness premise. -/
theorem exists_SU5_inclusion_of_simplyConnected [SimplyConnectedSpace SU5] :
    ∃ i : SU5 →* Group 10, Continuous i ∧ Function.Injective i ∧
      (projection 10).comp i = realification := by
  let := SU5_locallyPathConnected
  exact exists_SU5_inclusion_of_topology

end

end Math.CompactSpin
