import Physics.StandardModel.Operators.Support.Joint.SMJointAlgebraicSupport
import Physics.StandardModel.Operators.SMJointCoefficient
import Physics.StandardModel.Operators.SMComputableCharacter
import Physics.StandardModel.Operators.SMQLCompactMultiplicity
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Joint.SMJointAlgebraicSupport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMJointAlgebraicSupport.Occurs => Physics.SMJointAlgebraicSupport.Occurs,
  GUT.SMJointAlgebraicSupport.Occurs.eq_1 => Physics.SMJointAlgebraicSupport.Occurs.eq_1,
  GUT.SMJointAlgebraicSupport.balance => Physics.SMJointAlgebraicSupport.balance,
  GUT.SMJointAlgebraicSupport.balance.eq_1 => Physics.SMJointAlgebraicSupport.balance.eq_1,
  GUT.SMJointAlgebraicSupport.compactBorel => Physics.SMJointAlgebraicSupport.compactBorel,
  GUT.SMJointAlgebraicSupport.compactMeasurable => Physics.SMJointAlgebraicSupport.compactMeasurable,
  GUT.SMJointAlgebraicSupport.joint_allowed_iff => Physics.SMJointAlgebraicSupport.joint_allowed_iff,
  GUT.SMJointAlgebraicSupport.kernel_allowed_iff => Physics.SMJointAlgebraicSupport.kernel_allowed_iff,
  GUT.SMJointAlgebraicSupport.local_allowed_iff => Physics.SMJointAlgebraicSupport.local_allowed_iff,
  GUT.SMJointAlgebraicSupport.matches_iff => Physics.SMJointAlgebraicSupport.matches_iff,
  GUT.SMJointAlgebraicSupport.occurs_iff => Physics.SMJointAlgebraicSupport.occurs_iff,
  GUT.SMJointAlgebraicSupport.original_ql_forbidden => Physics.SMJointAlgebraicSupport.original_ql_forbidden,
  GUT.SMJointAlgebraicSupport.original_ql_iff => Physics.SMJointAlgebraicSupport.original_ql_iff,
  GUT.SMJointAlgebraicSupport.presents => Physics.SMJointAlgebraicSupport.presents,
  GUT.SMJointAlgebraicSupport.ql_test_iff => Physics.SMJointAlgebraicSupport.ql_test_iff,
  GUT.SMJointAlgebraicSupport.root_formula => Physics.SMJointAlgebraicSupport.root_formula,
  GUT.SMJointAlgebraicSupport.spinCoefficient => Physics.SMJointAlgebraicSupport.spinCoefficient,
  GUT.SMJointAlgebraicSupport.spinCoefficient.eq_1 => Physics.SMJointAlgebraicSupport.spinCoefficient.eq_1,
  GUT.SMJointAlgebraicSupport.spin_formula => Physics.SMJointAlgebraicSupport.spin_formula,
  GUT.SMJointAlgebraicSupport.terms_balance => Physics.SMJointAlgebraicSupport.terms_balance
]

assert_compatible GUT.SMJointAlgebraicSupport.Occurs => Physics.SMJointAlgebraicSupport.Occurs
assert_compatible GUT.SMJointAlgebraicSupport.Occurs.eq_1 => Physics.SMJointAlgebraicSupport.Occurs.eq_1
assert_compatible GUT.SMJointAlgebraicSupport.balance => Physics.SMJointAlgebraicSupport.balance
assert_compatible GUT.SMJointAlgebraicSupport.balance.eq_1 => Physics.SMJointAlgebraicSupport.balance.eq_1
assert_compatible GUT.SMJointAlgebraicSupport.compactBorel => Physics.SMJointAlgebraicSupport.compactBorel
assert_compatible GUT.SMJointAlgebraicSupport.compactMeasurable => Physics.SMJointAlgebraicSupport.compactMeasurable
assert_compatible GUT.SMJointAlgebraicSupport.joint_allowed_iff => Physics.SMJointAlgebraicSupport.joint_allowed_iff
assert_compatible GUT.SMJointAlgebraicSupport.kernel_allowed_iff => Physics.SMJointAlgebraicSupport.kernel_allowed_iff
assert_compatible GUT.SMJointAlgebraicSupport.local_allowed_iff => Physics.SMJointAlgebraicSupport.local_allowed_iff
assert_compatible GUT.SMJointAlgebraicSupport.matches_iff => Physics.SMJointAlgebraicSupport.matches_iff
assert_compatible GUT.SMJointAlgebraicSupport.occurs_iff => Physics.SMJointAlgebraicSupport.occurs_iff
assert_compatible GUT.SMJointAlgebraicSupport.original_ql_forbidden => Physics.SMJointAlgebraicSupport.original_ql_forbidden
assert_compatible GUT.SMJointAlgebraicSupport.original_ql_iff => Physics.SMJointAlgebraicSupport.original_ql_iff
assert_compatible GUT.SMJointAlgebraicSupport.presents => Physics.SMJointAlgebraicSupport.presents
assert_compatible GUT.SMJointAlgebraicSupport.ql_test_iff => Physics.SMJointAlgebraicSupport.ql_test_iff
assert_compatible GUT.SMJointAlgebraicSupport.root_formula => Physics.SMJointAlgebraicSupport.root_formula
assert_compatible GUT.SMJointAlgebraicSupport.spinCoefficient => Physics.SMJointAlgebraicSupport.spinCoefficient
assert_compatible GUT.SMJointAlgebraicSupport.spinCoefficient.eq_1 => Physics.SMJointAlgebraicSupport.spinCoefficient.eq_1
assert_compatible GUT.SMJointAlgebraicSupport.spin_formula => Physics.SMJointAlgebraicSupport.spin_formula
assert_compatible GUT.SMJointAlgebraicSupport.terms_balance => Physics.SMJointAlgebraicSupport.terms_balance
