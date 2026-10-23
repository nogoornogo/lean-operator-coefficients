import Physics.StandardModel.Operators.Support.Coordinates.SMGroupedCharacter
import Physics.StandardModel.Operators.SMNeutralSparseRanks
import Math.RepresentationTheory.GroupedExteriorPolynomial
import Math.RepresentationTheory.BoundedExteriorCoefficient
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMGroupedCharacter instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMGroupedCharacter.boundedCoefficient => Physics.SMGroupedCharacter.boundedCoefficient,
  GUT.SMGroupedCharacter.boundedCoefficient.eq_1 => Physics.SMGroupedCharacter.boundedCoefficient.eq_1,
  GUT.SMGroupedCharacter.boundedCoefficient_eq => Physics.SMGroupedCharacter.boundedCoefficient_eq,
  GUT.SMGroupedCharacter.groups => Physics.SMGroupedCharacter.groups,
  GUT.SMGroupedCharacter.groups_verified => Physics.SMGroupedCharacter.groups_verified,
  GUT.SMGroupedCharacter.linear => Physics.SMGroupedCharacter.linear,
  GUT.SMGroupedCharacter.solveBounded => Physics.SMGroupedCharacter.solveBounded,
  GUT.SMGroupedCharacter.solveBounded.eq_1 => Physics.SMGroupedCharacter.solveBounded.eq_1,
  GUT.SMGroupedCharacter.solveBounded_eq => Physics.SMGroupedCharacter.solveBounded_eq,
  GUT.SMGroupedCharacter.solveGrouped => Physics.SMGroupedCharacter.solveGrouped,
  GUT.SMGroupedCharacter.solveGrouped.eq_1 => Physics.SMGroupedCharacter.solveGrouped.eq_1,
  GUT.SMGroupedCharacter.solveGrouped_eq => Physics.SMGroupedCharacter.solveGrouped_eq,
  GUT.SMGroupedCharacter.source => Physics.SMGroupedCharacter.source,
  GUT.SMGroupedCharacter.source.eq_1 => Physics.SMGroupedCharacter.source.eq_1,
  GUT.SMGroupedCharacter.source_coefficient => Physics.SMGroupedCharacter.source_coefficient,
  GUT.SMGroupedCharacter.tests => Physics.SMGroupedCharacter.tests,
  GUT.SMKernelWeightData.tables.eq_1 => Physics.SMKernelWeightData.tables.eq_1,
  GUT.SMNeutralSparseRanks.solveDirectWith.eq_1 => Physics.SMNeutralSparseRanks.solveDirectWith.eq_1
]

assert_compatible GUT.SMGroupedCharacter.boundedCoefficient => Physics.SMGroupedCharacter.boundedCoefficient
assert_compatible GUT.SMGroupedCharacter.boundedCoefficient.eq_1 => Physics.SMGroupedCharacter.boundedCoefficient.eq_1
assert_compatible GUT.SMGroupedCharacter.boundedCoefficient_eq => Physics.SMGroupedCharacter.boundedCoefficient_eq
assert_compatible GUT.SMGroupedCharacter.groups => Physics.SMGroupedCharacter.groups
assert_compatible GUT.SMGroupedCharacter.groups_verified => Physics.SMGroupedCharacter.groups_verified
assert_compatible GUT.SMGroupedCharacter.linear => Physics.SMGroupedCharacter.linear
assert_compatible GUT.SMGroupedCharacter.solveBounded => Physics.SMGroupedCharacter.solveBounded
assert_compatible GUT.SMGroupedCharacter.solveBounded.eq_1 => Physics.SMGroupedCharacter.solveBounded.eq_1
assert_compatible GUT.SMGroupedCharacter.solveBounded_eq => Physics.SMGroupedCharacter.solveBounded_eq
assert_compatible GUT.SMGroupedCharacter.solveGrouped => Physics.SMGroupedCharacter.solveGrouped
assert_compatible GUT.SMGroupedCharacter.solveGrouped.eq_1 => Physics.SMGroupedCharacter.solveGrouped.eq_1
assert_compatible GUT.SMGroupedCharacter.solveGrouped_eq => Physics.SMGroupedCharacter.solveGrouped_eq
assert_compatible GUT.SMGroupedCharacter.source => Physics.SMGroupedCharacter.source
assert_compatible GUT.SMGroupedCharacter.source.eq_1 => Physics.SMGroupedCharacter.source.eq_1
assert_compatible GUT.SMGroupedCharacter.source_coefficient => Physics.SMGroupedCharacter.source_coefficient
assert_compatible GUT.SMGroupedCharacter.tests => Physics.SMGroupedCharacter.tests
assert_compatible GUT.SMKernelWeightData.tables.eq_1 => Physics.SMKernelWeightData.tables.eq_1
assert_compatible GUT.SMNeutralSparseRanks.solveDirectWith.eq_1 => Physics.SMNeutralSparseRanks.solveDirectWith.eq_1
