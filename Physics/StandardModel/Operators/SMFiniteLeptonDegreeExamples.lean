import Physics.StandardModel.Operators.Support.Decomposition.SMFiniteLeptonDegreeExamples
import Physics.StandardModel.Operators.SMFiniteLeptonDegreeBounds
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Decomposition.SMFiniteLeptonDegreeExamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMFiniteLeptonDegreeExamples.k101_minimum => Physics.SMFiniteLeptonDegreeExamples.k101_minimum,
  GUT.SMFiniteLeptonDegreeExamples.k101_none => Physics.SMFiniteLeptonDegreeExamples.k101_none,
  GUT.SMFiniteLeptonDegreeExamples.k3_b1_bounds => Physics.SMFiniteLeptonDegreeExamples.k3_b1_bounds,
  GUT.SMFiniteLeptonDegreeExamples.k4_b2_bounds => Physics.SMFiniteLeptonDegreeExamples.k4_b2_bounds,
  GUT.SMFiniteLeptonDegreeExamples.negative_baryon_bound => Physics.SMFiniteLeptonDegreeExamples.negative_baryon_bound
]

assert_compatible GUT.SMFiniteLeptonDegreeExamples.k101_minimum => Physics.SMFiniteLeptonDegreeExamples.k101_minimum
assert_compatible GUT.SMFiniteLeptonDegreeExamples.k101_none => Physics.SMFiniteLeptonDegreeExamples.k101_none
assert_compatible GUT.SMFiniteLeptonDegreeExamples.k3_b1_bounds => Physics.SMFiniteLeptonDegreeExamples.k3_b1_bounds
assert_compatible GUT.SMFiniteLeptonDegreeExamples.k4_b2_bounds => Physics.SMFiniteLeptonDegreeExamples.k4_b2_bounds
assert_compatible GUT.SMFiniteLeptonDegreeExamples.negative_baryon_bound => Physics.SMFiniteLeptonDegreeExamples.negative_baryon_bound
