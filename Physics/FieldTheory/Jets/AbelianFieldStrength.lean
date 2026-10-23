import Physics.FieldTheory.Jets.Gauge.AbelianFieldStrength
import Physics.FieldTheory.Jets.LorentzDirections
import Math.Algebra.JetCombined
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.AbelianFieldStrength instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.AbelianFieldStrength.Component => Physics.AbelianFieldStrength.Component,
  GUT.AbelianFieldStrength.Jets => Physics.AbelianFieldStrength.Jets,
  GUT.AbelianFieldStrength.Pair => Physics.AbelianFieldStrength.Pair,
  GUT.AbelianFieldStrength.Triple => Physics.AbelianFieldStrength.Triple,
  GUT.AbelianFieldStrength.V => Physics.AbelianFieldStrength.V,
  GUT.AbelianFieldStrength.basis => Physics.AbelianFieldStrength.basis,
  GUT.AbelianFieldStrength.basis.eq_1 => Physics.AbelianFieldStrength.basis.eq_1,
  GUT.AbelianFieldStrength.canonical_identity => Physics.AbelianFieldStrength.canonical_identity,
  GUT.AbelianFieldStrength.directional => Physics.AbelianFieldStrength.directional,
  GUT.AbelianFieldStrength.directional.eq_1 => Physics.AbelianFieldStrength.directional.eq_1,
  GUT.AbelianFieldStrength.directionalMap => Physics.AbelianFieldStrength.directionalMap,
  GUT.AbelianFieldStrength.directional_apply => Physics.AbelianFieldStrength.directional_apply,
  GUT.AbelianFieldStrength.directional_covariant => Physics.AbelianFieldStrength.directional_covariant,
  GUT.AbelianFieldStrength.directional_single => Physics.AbelianFieldStrength.directional_single,
  GUT.AbelianFieldStrength.field => Physics.AbelianFieldStrength.field,
  GUT.AbelianFieldStrength.field_pair => Physics.AbelianFieldStrength.field_pair,
  GUT.AbelianFieldStrength.form => Physics.AbelianFieldStrength.form,
  GUT.AbelianFieldStrength.form.eq_1 => Physics.AbelianFieldStrength.form.eq_1,
  GUT.AbelianFieldStrength.form_invariant => Physics.AbelianFieldStrength.form_invariant,
  GUT.AbelianFieldStrength.metric => Physics.AbelianFieldStrength.metric,
  GUT.AbelianFieldStrength.metric_apply => Physics.AbelianFieldStrength.metric_apply,
  GUT.AbelianFieldStrength.metric_basis => Physics.AbelianFieldStrength.metric_basis,
  GUT.AbelianFieldStrength.metric_covariant => Physics.AbelianFieldStrength.metric_covariant,
  GUT.AbelianFieldStrength.pair => Physics.AbelianFieldStrength.pair,
  GUT.AbelianFieldStrength.pair.eq_1 => Physics.AbelianFieldStrength.pair.eq_1,
  GUT.AbelianFieldStrength.pairBasis => Physics.AbelianFieldStrength.pairBasis,
  GUT.AbelianFieldStrength.pairBasis.eq_1 => Physics.AbelianFieldStrength.pairBasis.eq_1,
  GUT.AbelianFieldStrength.pair_apply => Physics.AbelianFieldStrength.pair_apply,
  GUT.AbelianFieldStrength.pair_basis => Physics.AbelianFieldStrength.pair_basis,
  GUT.AbelianFieldStrength.sign => Physics.AbelianFieldStrength.sign,
  GUT.AbelianFieldStrength.sign.eq_1 => Physics.AbelianFieldStrength.sign.eq_1,
  GUT.AbelianFieldStrength.vector_expand => Physics.AbelianFieldStrength.vector_expand,
  GUT.AbelianFieldStrength.zeroPair => Physics.AbelianFieldStrength.zeroPair,
  GUT.AbelianFieldStrength.zeroPair.eq_1 => Physics.AbelianFieldStrength.zeroPair.eq_1,
  GUT.AbelianFieldStrength.zeroPair_covariant => Physics.AbelianFieldStrength.zeroPair_covariant
]

assert_compatible GUT.AbelianFieldStrength.Component => Physics.AbelianFieldStrength.Component
assert_compatible GUT.AbelianFieldStrength.Jets => Physics.AbelianFieldStrength.Jets
assert_compatible GUT.AbelianFieldStrength.Pair => Physics.AbelianFieldStrength.Pair
assert_compatible GUT.AbelianFieldStrength.Triple => Physics.AbelianFieldStrength.Triple
assert_compatible GUT.AbelianFieldStrength.V => Physics.AbelianFieldStrength.V
assert_compatible GUT.AbelianFieldStrength.basis => Physics.AbelianFieldStrength.basis
assert_compatible GUT.AbelianFieldStrength.basis.eq_1 => Physics.AbelianFieldStrength.basis.eq_1
assert_compatible GUT.AbelianFieldStrength.canonical_identity => Physics.AbelianFieldStrength.canonical_identity
assert_compatible GUT.AbelianFieldStrength.directional => Physics.AbelianFieldStrength.directional
assert_compatible GUT.AbelianFieldStrength.directional.eq_1 => Physics.AbelianFieldStrength.directional.eq_1
assert_compatible GUT.AbelianFieldStrength.directionalMap => Physics.AbelianFieldStrength.directionalMap
assert_compatible GUT.AbelianFieldStrength.directional_apply => Physics.AbelianFieldStrength.directional_apply
assert_compatible GUT.AbelianFieldStrength.directional_covariant => Physics.AbelianFieldStrength.directional_covariant
assert_compatible GUT.AbelianFieldStrength.directional_single => Physics.AbelianFieldStrength.directional_single
assert_compatible GUT.AbelianFieldStrength.field => Physics.AbelianFieldStrength.field
assert_compatible GUT.AbelianFieldStrength.field_pair => Physics.AbelianFieldStrength.field_pair
assert_compatible GUT.AbelianFieldStrength.form => Physics.AbelianFieldStrength.form
assert_compatible GUT.AbelianFieldStrength.form.eq_1 => Physics.AbelianFieldStrength.form.eq_1
assert_compatible GUT.AbelianFieldStrength.form_invariant => Physics.AbelianFieldStrength.form_invariant
assert_compatible GUT.AbelianFieldStrength.metric => Physics.AbelianFieldStrength.metric
assert_compatible GUT.AbelianFieldStrength.metric_apply => Physics.AbelianFieldStrength.metric_apply
assert_compatible GUT.AbelianFieldStrength.metric_basis => Physics.AbelianFieldStrength.metric_basis
assert_compatible GUT.AbelianFieldStrength.metric_covariant => Physics.AbelianFieldStrength.metric_covariant
assert_compatible GUT.AbelianFieldStrength.pair => Physics.AbelianFieldStrength.pair
assert_compatible GUT.AbelianFieldStrength.pair.eq_1 => Physics.AbelianFieldStrength.pair.eq_1
assert_compatible GUT.AbelianFieldStrength.pairBasis => Physics.AbelianFieldStrength.pairBasis
assert_compatible GUT.AbelianFieldStrength.pairBasis.eq_1 => Physics.AbelianFieldStrength.pairBasis.eq_1
assert_compatible GUT.AbelianFieldStrength.pair_apply => Physics.AbelianFieldStrength.pair_apply
assert_compatible GUT.AbelianFieldStrength.pair_basis => Physics.AbelianFieldStrength.pair_basis
assert_compatible GUT.AbelianFieldStrength.sign => Physics.AbelianFieldStrength.sign
assert_compatible GUT.AbelianFieldStrength.sign.eq_1 => Physics.AbelianFieldStrength.sign.eq_1
assert_compatible GUT.AbelianFieldStrength.vector_expand => Physics.AbelianFieldStrength.vector_expand
assert_compatible GUT.AbelianFieldStrength.zeroPair => Physics.AbelianFieldStrength.zeroPair
assert_compatible GUT.AbelianFieldStrength.zeroPair.eq_1 => Physics.AbelianFieldStrength.zeroPair.eq_1
assert_compatible GUT.AbelianFieldStrength.zeroPair_covariant => Physics.AbelianFieldStrength.zeroPair_covariant
