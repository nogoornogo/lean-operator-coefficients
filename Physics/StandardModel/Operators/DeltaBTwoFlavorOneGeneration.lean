import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorOneGeneration
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.SixQuarkFlavorOneGeneration
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorOneGeneration instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DeltaBTwoFlavorOneGeneration.add => Physics.DeltaBTwoFlavorOneGeneration.add,
  GUT.DeltaBTwoFlavorOneGeneration.finrank_hom => Physics.DeltaBTwoFlavorOneGeneration.finrank_hom,
  GUT.DeltaBTwoFlavorOneGeneration.finrank_onFields => Physics.DeltaBTwoFlavorOneGeneration.finrank_onFields,
  GUT.DeltaBTwoFlavorOneGeneration.finrank_physical => Physics.DeltaBTwoFlavorOneGeneration.finrank_physical,
  GUT.DeltaBTwoFlavorOneGeneration.forget => Physics.DeltaBTwoFlavorOneGeneration.forget,
  GUT.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv => Physics.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv,
  GUT.DeltaBTwoFlavorOneGeneration.inverse_twoProbes => Physics.DeltaBTwoFlavorOneGeneration.inverse_twoProbes,
  GUT.DeltaBTwoFlavorOneGeneration.onFieldsTwoProbeEquiv => Physics.DeltaBTwoFlavorOneGeneration.onFieldsTwoProbeEquiv,
  GUT.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv => Physics.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv,
  GUT.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv_symm_apply => Physics.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv_symm_apply,
  GUT.DeltaBTwoFlavorOneGeneration.scalar => Physics.DeltaBTwoFlavorOneGeneration.scalar,
  GUT.DeltaBTwoFlavorOneGeneration.scalarFiber => Physics.DeltaBTwoFlavorOneGeneration.scalarFiber,
  GUT.DeltaBTwoFlavorOneGeneration.strip => Physics.DeltaBTwoFlavorOneGeneration.strip,
  GUT.DeltaBTwoFlavorOneGeneration.strip.eq_1 => Physics.DeltaBTwoFlavorOneGeneration.strip.eq_1,
  GUT.DeltaBTwoFlavorOneGeneration.strip_exchange => Physics.DeltaBTwoFlavorOneGeneration.strip_exchange,
  GUT.DeltaBTwoFlavorOneGeneration.strip_exchange_symm => Physics.DeltaBTwoFlavorOneGeneration.strip_exchange_symm,
  GUT.DeltaBTwoFlavorOneGeneration.strip_map => Physics.DeltaBTwoFlavorOneGeneration.strip_map,
  GUT.DeltaBTwoFlavorOneGeneration.strip_symm_map => Physics.DeltaBTwoFlavorOneGeneration.strip_symm_map,
  GUT.DeltaBTwoFlavorOneGeneration.typedScalarEquiv => Physics.DeltaBTwoFlavorOneGeneration.typedScalarEquiv
]

assert_compatible GUT.DeltaBTwoFlavorOneGeneration.add => Physics.DeltaBTwoFlavorOneGeneration.add
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.finrank_hom => Physics.DeltaBTwoFlavorOneGeneration.finrank_hom
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.finrank_onFields => Physics.DeltaBTwoFlavorOneGeneration.finrank_onFields
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.finrank_physical => Physics.DeltaBTwoFlavorOneGeneration.finrank_physical
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.forget => Physics.DeltaBTwoFlavorOneGeneration.forget
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv => Physics.DeltaBTwoFlavorOneGeneration.homTwoProbeEquiv
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.inverse_twoProbes => Physics.DeltaBTwoFlavorOneGeneration.inverse_twoProbes
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.onFieldsTwoProbeEquiv => Physics.DeltaBTwoFlavorOneGeneration.onFieldsTwoProbeEquiv
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv => Physics.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv_symm_apply => Physics.DeltaBTwoFlavorOneGeneration.physicalTwoProbeEquiv_symm_apply
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.scalar => Physics.DeltaBTwoFlavorOneGeneration.scalar
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.scalarFiber => Physics.DeltaBTwoFlavorOneGeneration.scalarFiber
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.strip => Physics.DeltaBTwoFlavorOneGeneration.strip
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.strip.eq_1 => Physics.DeltaBTwoFlavorOneGeneration.strip.eq_1
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.strip_exchange => Physics.DeltaBTwoFlavorOneGeneration.strip_exchange
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.strip_exchange_symm => Physics.DeltaBTwoFlavorOneGeneration.strip_exchange_symm
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.strip_map => Physics.DeltaBTwoFlavorOneGeneration.strip_map
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.strip_symm_map => Physics.DeltaBTwoFlavorOneGeneration.strip_symm_map
assert_compatible GUT.DeltaBTwoFlavorOneGeneration.typedScalarEquiv => Physics.DeltaBTwoFlavorOneGeneration.typedScalarEquiv
