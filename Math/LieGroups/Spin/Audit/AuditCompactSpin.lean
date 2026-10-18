import Math.Audit.ImportOrigin
import Math.LieGroups.Spin.SU5LiftPreparation

/-! Compile and audit the actual compact real carrier and its double cover.
This checkpoint is not the SU(5) inclusion theorem. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Compact Spin foundation imports another gauge family: {mod}"

namespace Math.CompactSpin.Audit

example : CompactSpace (Group 10) := compact 10
example : PathConnectedSpace (Group 10) := pathConnected 8
example : IsCoveringMap (projection 10) := projection_covering 10
example (g : Orthogonal 10) : Nat.card ((projection 10) ⁻¹' {g}) = 2 :=
  projection_fiber_card 10 g
example : ¬ Function.Injective (projection 10) := projection_not_injective 10

#print axioms projection_surjective
#print axioms projection_continuous
#print axioms projection_covering
#print axioms projection_fiber_card
#print axioms projection_not_injective
#print axioms compact
#print axioms pathConnected
#print axioms Math.CoveringHom.existsUnique_lift
#print axioms Math.CoveringHom.injective_of_comp
#print axioms existsUnique_lift
#print axioms exists_injective_lift
#print axioms realification
#print axioms realification_continuous
#print axioms realification_injective
#print axioms realification_isClosedEmbedding
#print axioms exists_SU5_inclusion_of_topology
#print axioms SU5_locallyPathConnected
#print axioms exists_SU5_inclusion_of_simplyConnected

end Math.CompactSpin.Audit
