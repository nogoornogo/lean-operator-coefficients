import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkQuotient
import Physics.StandardModel.Operators.HeeckLeSixQuarkBlocks
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkQuotient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkQuotient.Coeff => Physics.HeeckLeSixQuarkQuotient.Coeff,
  GUT.HeeckLeSixQuarkQuotient.Output => Physics.HeeckLeSixQuarkQuotient.Output,
  GUT.HeeckLeSixQuarkQuotient.forward => Physics.HeeckLeSixQuarkQuotient.forward,
  GUT.HeeckLeSixQuarkQuotient.forward.eq_1 => Physics.HeeckLeSixQuarkQuotient.forward.eq_1,
  GUT.HeeckLeSixQuarkQuotient.forward_solve => Physics.HeeckLeSixQuarkQuotient.forward_solve,
  GUT.HeeckLeSixQuarkQuotient.kernelFirst => Physics.HeeckLeSixQuarkQuotient.kernelFirst,
  GUT.HeeckLeSixQuarkQuotient.kernelFirst.eq_1 => Physics.HeeckLeSixQuarkQuotient.kernelFirst.eq_1,
  GUT.HeeckLeSixQuarkQuotient.kernelSecond => Physics.HeeckLeSixQuarkQuotient.kernelSecond,
  GUT.HeeckLeSixQuarkQuotient.kernelSecond.eq_1 => Physics.HeeckLeSixQuarkQuotient.kernelSecond.eq_1,
  GUT.HeeckLeSixQuarkQuotient.sectionLinear => Physics.HeeckLeSixQuarkQuotient.sectionLinear,
  GUT.HeeckLeSixQuarkQuotient.sectionMap => Physics.HeeckLeSixQuarkQuotient.sectionMap,
  GUT.HeeckLeSixQuarkQuotient.sectionMap.eq_1 => Physics.HeeckLeSixQuarkQuotient.sectionMap.eq_1,
  GUT.HeeckLeSixQuarkQuotient.section_linear_add => Physics.HeeckLeSixQuarkQuotient.section_linear_add,
  GUT.HeeckLeSixQuarkQuotient.section_linear_smul => Physics.HeeckLeSixQuarkQuotient.section_linear_smul,
  GUT.HeeckLeSixQuarkQuotient.solve => Physics.HeeckLeSixQuarkQuotient.solve,
  GUT.HeeckLeSixQuarkQuotient.solve.eq_1 => Physics.HeeckLeSixQuarkQuotient.solve.eq_1,
  GUT.HeeckLeSixQuarkQuotient.solve_forward => Physics.HeeckLeSixQuarkQuotient.solve_forward,
  GUT.HeeckLeSixQuarkQuotient.solve_free => Physics.HeeckLeSixQuarkQuotient.solve_free
]

assert_compatible GUT.HeeckLeSixQuarkQuotient.Coeff => Physics.HeeckLeSixQuarkQuotient.Coeff
assert_compatible GUT.HeeckLeSixQuarkQuotient.Output => Physics.HeeckLeSixQuarkQuotient.Output
assert_compatible GUT.HeeckLeSixQuarkQuotient.forward => Physics.HeeckLeSixQuarkQuotient.forward
assert_compatible GUT.HeeckLeSixQuarkQuotient.forward.eq_1 => Physics.HeeckLeSixQuarkQuotient.forward.eq_1
assert_compatible GUT.HeeckLeSixQuarkQuotient.forward_solve => Physics.HeeckLeSixQuarkQuotient.forward_solve
assert_compatible GUT.HeeckLeSixQuarkQuotient.kernelFirst => Physics.HeeckLeSixQuarkQuotient.kernelFirst
assert_compatible GUT.HeeckLeSixQuarkQuotient.kernelFirst.eq_1 => Physics.HeeckLeSixQuarkQuotient.kernelFirst.eq_1
assert_compatible GUT.HeeckLeSixQuarkQuotient.kernelSecond => Physics.HeeckLeSixQuarkQuotient.kernelSecond
assert_compatible GUT.HeeckLeSixQuarkQuotient.kernelSecond.eq_1 => Physics.HeeckLeSixQuarkQuotient.kernelSecond.eq_1
assert_compatible GUT.HeeckLeSixQuarkQuotient.sectionLinear => Physics.HeeckLeSixQuarkQuotient.sectionLinear
assert_compatible GUT.HeeckLeSixQuarkQuotient.sectionMap => Physics.HeeckLeSixQuarkQuotient.sectionMap
assert_compatible GUT.HeeckLeSixQuarkQuotient.sectionMap.eq_1 => Physics.HeeckLeSixQuarkQuotient.sectionMap.eq_1
assert_compatible GUT.HeeckLeSixQuarkQuotient.section_linear_add => Physics.HeeckLeSixQuarkQuotient.section_linear_add
assert_compatible GUT.HeeckLeSixQuarkQuotient.section_linear_smul => Physics.HeeckLeSixQuarkQuotient.section_linear_smul
assert_compatible GUT.HeeckLeSixQuarkQuotient.solve => Physics.HeeckLeSixQuarkQuotient.solve
assert_compatible GUT.HeeckLeSixQuarkQuotient.solve.eq_1 => Physics.HeeckLeSixQuarkQuotient.solve.eq_1
assert_compatible GUT.HeeckLeSixQuarkQuotient.solve_forward => Physics.HeeckLeSixQuarkQuotient.solve_forward
assert_compatible GUT.HeeckLeSixQuarkQuotient.solve_free => Physics.HeeckLeSixQuarkQuotient.solve_free
