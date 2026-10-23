import Physics.StandardModel.Operators.Support.Coordinates.SMHiggsConstituents
import Math.RepresentationTheory.TwistedSU2ClebschGordan
import Physics.StandardModel.Operators.NeutralHiggsPowers
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMHiggsConstituents instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMHiggsConstituents.Bosons => Physics.SMHiggsConstituents.Bosons,
  GUT.SMHiggsConstituents.character => Physics.SMHiggsConstituents.character,
  GUT.SMHiggsConstituents.character_apply => Physics.SMHiggsConstituents.character_apply,
  GUT.SMHiggsConstituents.common_charge => Physics.SMHiggsConstituents.common_charge,
  GUT.SMHiggsConstituents.equivalence => Physics.SMHiggsConstituents.equivalence,
  GUT.SMHiggsConstituents.higgsEquiv => Physics.SMHiggsConstituents.higgsEquiv,
  GUT.SMHiggsConstituents.higgs_eq => Physics.SMHiggsConstituents.higgs_eq,
  GUT.SMHiggsConstituents.hyperProjection => Physics.SMHiggsConstituents.hyperProjection,
  GUT.SMHiggsConstituents.weakProjection => Physics.SMHiggsConstituents.weakProjection
]

assert_compatible GUT.SMHiggsConstituents.Bosons => Physics.SMHiggsConstituents.Bosons
assert_compatible GUT.SMHiggsConstituents.character => Physics.SMHiggsConstituents.character
assert_compatible GUT.SMHiggsConstituents.character_apply => Physics.SMHiggsConstituents.character_apply
assert_compatible GUT.SMHiggsConstituents.common_charge => Physics.SMHiggsConstituents.common_charge
assert_compatible GUT.SMHiggsConstituents.equivalence => Physics.SMHiggsConstituents.equivalence
assert_compatible GUT.SMHiggsConstituents.higgsEquiv => Physics.SMHiggsConstituents.higgsEquiv
assert_compatible GUT.SMHiggsConstituents.higgs_eq => Physics.SMHiggsConstituents.higgs_eq
assert_compatible GUT.SMHiggsConstituents.hyperProjection => Physics.SMHiggsConstituents.hyperProjection
assert_compatible GUT.SMHiggsConstituents.weakProjection => Physics.SMHiggsConstituents.weakProjection
