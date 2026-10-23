import Physics.StandardModel.Operators.Support.Joint.SMJointSupportDataExamples
import Physics.StandardModel.Operators.SMJointSupportData
import Physics.StandardModel.Operators.SMMixedFamilySupport
import Physics.StandardModel.Operators.SMChiralitySupport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointSupportDataExamples instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointSupportDataExamples.component_to_support => Physics.SMJointSupportDataExamples.component_to_support,
  GUT.SMJointSupportDataExamples.mixedPattern => Physics.SMJointSupportDataExamples.mixedPattern,
  GUT.SMJointSupportDataExamples.mixed_allowed => Physics.SMJointSupportDataExamples.mixed_allowed,
  GUT.SMJointSupportDataExamples.mixed_data_witness => Physics.SMJointSupportDataExamples.mixed_data_witness,
  GUT.SMJointSupportDataExamples.oppositePair => Physics.SMJointSupportDataExamples.oppositePair,
  GUT.SMJointSupportDataExamples.oppositePair.eq_1 => Physics.SMJointSupportDataExamples.oppositePair.eq_1,
  GUT.SMJointSupportDataExamples.oppositePair_forbidden => Physics.SMJointSupportDataExamples.oppositePair_forbidden,
  GUT.SMJointSupportDataExamples.oppositePair_no_data => Physics.SMJointSupportDataExamples.oppositePair_no_data,
  GUT.SMJointSupportDataExamples.original_of_data => Physics.SMJointSupportDataExamples.original_of_data,
  GUT.SMJointSupportDataExamples.q18Pattern => Physics.SMJointSupportDataExamples.q18Pattern,
  GUT.SMJointSupportDataExamples.q18_allowed => Physics.SMJointSupportDataExamples.q18_allowed,
  GUT.SMJointSupportDataExamples.q18_data_witness => Physics.SMJointSupportDataExamples.q18_data_witness
]

assert_compatible GUT.SMJointSupportDataExamples.component_to_support => Physics.SMJointSupportDataExamples.component_to_support
assert_compatible GUT.SMJointSupportDataExamples.mixedPattern => Physics.SMJointSupportDataExamples.mixedPattern
assert_compatible GUT.SMJointSupportDataExamples.mixed_allowed => Physics.SMJointSupportDataExamples.mixed_allowed
assert_compatible GUT.SMJointSupportDataExamples.mixed_data_witness => Physics.SMJointSupportDataExamples.mixed_data_witness
assert_compatible GUT.SMJointSupportDataExamples.oppositePair => Physics.SMJointSupportDataExamples.oppositePair
assert_compatible GUT.SMJointSupportDataExamples.oppositePair.eq_1 => Physics.SMJointSupportDataExamples.oppositePair.eq_1
assert_compatible GUT.SMJointSupportDataExamples.oppositePair_forbidden => Physics.SMJointSupportDataExamples.oppositePair_forbidden
assert_compatible GUT.SMJointSupportDataExamples.oppositePair_no_data => Physics.SMJointSupportDataExamples.oppositePair_no_data
assert_compatible GUT.SMJointSupportDataExamples.original_of_data => Physics.SMJointSupportDataExamples.original_of_data
assert_compatible GUT.SMJointSupportDataExamples.q18Pattern => Physics.SMJointSupportDataExamples.q18Pattern
assert_compatible GUT.SMJointSupportDataExamples.q18_allowed => Physics.SMJointSupportDataExamples.q18_allowed
assert_compatible GUT.SMJointSupportDataExamples.q18_data_witness => Physics.SMJointSupportDataExamples.q18_data_witness
