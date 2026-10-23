import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarInputAdapter
import Math.RepresentationTheory.JetInputAdapter
import Physics.FieldTheory.Jets.PolynomialScalarEOM
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Scalar.Inputs.ScalarInputAdapter instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.ScalarInputAdapter.Input => Physics.ScalarInputAdapter.Input,
  GUT.ScalarInputAdapter.LorentzInput => Physics.ScalarInputAdapter.LorentzInput,
  GUT.ScalarInputAdapter.action => Physics.ScalarInputAdapter.action,
  GUT.ScalarInputAdapter.admissible_iff => Physics.ScalarInputAdapter.admissible_iff,
  GUT.ScalarInputAdapter.equiv => Physics.ScalarInputAdapter.equiv,
  GUT.ScalarInputAdapter.extraction => Physics.ScalarInputAdapter.extraction,
  GUT.ScalarInputAdapter.interaction_constraint => Physics.ScalarInputAdapter.interaction_constraint,
  GUT.ScalarInputAdapter.lorentzAction => Physics.ScalarInputAdapter.lorentzAction,
  GUT.ScalarInputAdapter.lorentzEquiv => Physics.ScalarInputAdapter.lorentzEquiv,
  GUT.ScalarInputAdapter.lorentz_extraction => Physics.ScalarInputAdapter.lorentz_extraction,
  GUT.ScalarInputAdapter.lorentz_interaction_constraint => Physics.ScalarInputAdapter.lorentz_interaction_constraint,
  GUT.ScalarInputAdapter.lorentz_stable => Physics.ScalarInputAdapter.lorentz_stable,
  GUT.ScalarInputAdapter.nonzero_iff => Physics.ScalarInputAdapter.nonzero_iff,
  GUT.ScalarInputAdapter.reconstruction => Physics.ScalarInputAdapter.reconstruction,
  GUT.ScalarInputAdapter.stable => Physics.ScalarInputAdapter.stable
]

assert_compatible GUT.ScalarInputAdapter.Input => Physics.ScalarInputAdapter.Input
assert_compatible GUT.ScalarInputAdapter.LorentzInput => Physics.ScalarInputAdapter.LorentzInput
assert_compatible GUT.ScalarInputAdapter.action => Physics.ScalarInputAdapter.action
assert_compatible GUT.ScalarInputAdapter.admissible_iff => Physics.ScalarInputAdapter.admissible_iff
assert_compatible GUT.ScalarInputAdapter.equiv => Physics.ScalarInputAdapter.equiv
assert_compatible GUT.ScalarInputAdapter.extraction => Physics.ScalarInputAdapter.extraction
assert_compatible GUT.ScalarInputAdapter.interaction_constraint => Physics.ScalarInputAdapter.interaction_constraint
assert_compatible GUT.ScalarInputAdapter.lorentzAction => Physics.ScalarInputAdapter.lorentzAction
assert_compatible GUT.ScalarInputAdapter.lorentzEquiv => Physics.ScalarInputAdapter.lorentzEquiv
assert_compatible GUT.ScalarInputAdapter.lorentz_extraction => Physics.ScalarInputAdapter.lorentz_extraction
assert_compatible GUT.ScalarInputAdapter.lorentz_interaction_constraint => Physics.ScalarInputAdapter.lorentz_interaction_constraint
assert_compatible GUT.ScalarInputAdapter.lorentz_stable => Physics.ScalarInputAdapter.lorentz_stable
assert_compatible GUT.ScalarInputAdapter.nonzero_iff => Physics.ScalarInputAdapter.nonzero_iff
assert_compatible GUT.ScalarInputAdapter.reconstruction => Physics.ScalarInputAdapter.reconstruction
assert_compatible GUT.ScalarInputAdapter.stable => Physics.ScalarInputAdapter.stable
