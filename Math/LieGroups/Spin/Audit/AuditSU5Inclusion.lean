import Math.Audit.ImportOrigin
import Math.LieGroups.Spin.SU5Inclusion
import Math.LieGroups.SpecialUnitary.Audit.AuditSpecialUnitaryRealification

/-! Actual compact inclusion, unique continuous lift, and a nonidentity image.
No SU(5) matter model or SU(6) proof may supply the mathematical inclusion. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Compact Spin inclusion imports another gauge family: {mod}"

namespace Math.CompactSpin.Audit

noncomputable section

example : SimplyConnectedSpace SU5 := SU5_simplyConnected
example : LocallyPathConnectedSpace SU5 := SU5_locallyPathConnected
example : Topology.IsClosedEmbedding SU5Inclusion := SU5Inclusion_isClosedEmbedding
example : (projection 10).comp SU5Inclusion = realification := projection_comp_SU5Inclusion
example (i : SU5 →* Group 10) (hc : Continuous i)
    (hp : (projection 10).comp i = realification) : i = SU5Inclusion :=
  SU5Inclusion_unique i hc hp
example : continuousSU5Inclusion.toMonoidHom = SU5Inclusion := rfl

def nontrivialSU5 : SU5 :=
  SUN.Block.inclusion 2 3 SpecialUnitaryRealification.Audit.minusTwo

theorem nontrivialSU5_ne_one : nontrivialSU5 ≠ 1 := by
  intro h
  apply SpecialUnitaryRealification.Audit.minusTwo_ne_one
  exact SUN.Block.inclusion_injective 2 3 (h.trans (map_one (SUN.Block.inclusion 2 3)).symm)

theorem SU5Inclusion_nontrivial : SU5Inclusion nontrivialSU5 ≠ 1 := by
  intro h
  apply nontrivialSU5_ne_one
  exact SU5Inclusion_injective (h.trans (map_one SU5Inclusion).symm)

example : ¬ Function.Injective (projection 10) := projection_not_injective 10

#print axioms SU5_simplyConnected
#print axioms exists_SU5_inclusion
#print axioms SU5Inclusion
#print axioms SU5Inclusion_continuous
#print axioms SU5Inclusion_injective
#print axioms projection_comp_SU5Inclusion
#print axioms SU5Inclusion_isClosedEmbedding
#print axioms continuousSU5Inclusion
#print axioms SU5Inclusion_unique
#print axioms nontrivialSU5_ne_one
#print axioms SU5Inclusion_nontrivial

end

end Math.CompactSpin.Audit
