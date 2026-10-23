import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlOrderedCompleteness
import Physics.StandardModel.Gauge.QqqlGaugeRegroup
import Physics.StandardModel.Operators.QqqlLocalCompleteness
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlOrderedCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FourWeakWeylCompleteness.pairing.eq_1 => Physics.FourWeakWeylCompleteness.pairing.eq_1,
  GUT.QqqlLocalCompleteness.pairing.eq_1 => Physics.QqqlLocalCompleteness.pairing.eq_1,
  GUT.QqqlOrderedCompleteness.Coefficient => Physics.QqqlOrderedCompleteness.Coefficient,
  GUT.QqqlOrderedCompleteness.PhysicalGroup => Physics.QqqlOrderedCompleteness.PhysicalGroup,
  GUT.QqqlOrderedCompleteness.Residual => Physics.QqqlOrderedCompleteness.Residual,
  GUT.QqqlOrderedCompleteness.assemble_apply => Physics.QqqlOrderedCompleteness.assemble_apply,
  GUT.QqqlOrderedCompleteness.associate => Physics.QqqlOrderedCompleteness.associate,
  GUT.QqqlOrderedCompleteness.descend => Physics.QqqlOrderedCompleteness.descend,
  GUT.QqqlOrderedCompleteness.fields => Physics.QqqlOrderedCompleteness.fields,
  GUT.QqqlOrderedCompleteness.flavor => Physics.QqqlOrderedCompleteness.flavor,
  GUT.QqqlOrderedCompleteness.homEquiv => Physics.QqqlOrderedCompleteness.homEquiv,
  GUT.QqqlOrderedCompleteness.leptonSpin => Physics.QqqlOrderedCompleteness.leptonSpin,
  GUT.QqqlOrderedCompleteness.localFields => Physics.QqqlOrderedCompleteness.localFields,
  GUT.QqqlOrderedCompleteness.localProjection => Physics.QqqlOrderedCompleteness.localProjection,
  GUT.QqqlOrderedCompleteness.localProjection_surjective => Physics.QqqlOrderedCompleteness.localProjection_surjective,
  GUT.QqqlOrderedCompleteness.localRegroup => Physics.QqqlOrderedCompleteness.localRegroup,
  GUT.QqqlOrderedCompleteness.projection => Physics.QqqlOrderedCompleteness.projection,
  GUT.QqqlOrderedCompleteness.projection_surjective => Physics.QqqlOrderedCompleteness.projection_surjective,
  GUT.QqqlOrderedCompleteness.quarkSpin => Physics.QqqlOrderedCompleteness.quarkSpin,
  GUT.QqqlOrderedCompleteness.regroup => Physics.QqqlOrderedCompleteness.regroup
]

assert_compatible GUT.FourWeakWeylCompleteness.pairing.eq_1 => Physics.FourWeakWeylCompleteness.pairing.eq_1
assert_compatible GUT.QqqlLocalCompleteness.pairing.eq_1 => Physics.QqqlLocalCompleteness.pairing.eq_1
assert_compatible GUT.QqqlOrderedCompleteness.Coefficient => Physics.QqqlOrderedCompleteness.Coefficient
assert_compatible GUT.QqqlOrderedCompleteness.PhysicalGroup => Physics.QqqlOrderedCompleteness.PhysicalGroup
assert_compatible GUT.QqqlOrderedCompleteness.Residual => Physics.QqqlOrderedCompleteness.Residual
assert_compatible GUT.QqqlOrderedCompleteness.assemble_apply => Physics.QqqlOrderedCompleteness.assemble_apply
assert_compatible GUT.QqqlOrderedCompleteness.associate => Physics.QqqlOrderedCompleteness.associate
assert_compatible GUT.QqqlOrderedCompleteness.descend => Physics.QqqlOrderedCompleteness.descend
assert_compatible GUT.QqqlOrderedCompleteness.fields => Physics.QqqlOrderedCompleteness.fields
assert_compatible GUT.QqqlOrderedCompleteness.flavor => Physics.QqqlOrderedCompleteness.flavor
assert_compatible GUT.QqqlOrderedCompleteness.homEquiv => Physics.QqqlOrderedCompleteness.homEquiv
assert_compatible GUT.QqqlOrderedCompleteness.leptonSpin => Physics.QqqlOrderedCompleteness.leptonSpin
assert_compatible GUT.QqqlOrderedCompleteness.localFields => Physics.QqqlOrderedCompleteness.localFields
assert_compatible GUT.QqqlOrderedCompleteness.localProjection => Physics.QqqlOrderedCompleteness.localProjection
assert_compatible GUT.QqqlOrderedCompleteness.localProjection_surjective => Physics.QqqlOrderedCompleteness.localProjection_surjective
assert_compatible GUT.QqqlOrderedCompleteness.localRegroup => Physics.QqqlOrderedCompleteness.localRegroup
assert_compatible GUT.QqqlOrderedCompleteness.projection => Physics.QqqlOrderedCompleteness.projection
assert_compatible GUT.QqqlOrderedCompleteness.projection_surjective => Physics.QqqlOrderedCompleteness.projection_surjective
assert_compatible GUT.QqqlOrderedCompleteness.quarkSpin => Physics.QqqlOrderedCompleteness.quarkSpin
assert_compatible GUT.QqqlOrderedCompleteness.regroup => Physics.QqqlOrderedCompleteness.regroup
