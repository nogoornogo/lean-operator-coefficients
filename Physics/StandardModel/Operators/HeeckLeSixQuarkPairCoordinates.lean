import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairCoordinates
import Physics.StandardModel.Operators.HeeckLeSixQuarkAssemblyBase
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkPairCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkPairCoordinates.couplingAssembly => Physics.HeeckLeSixQuarkPairCoordinates.couplingAssembly,
  GUT.HeeckLeSixQuarkPairCoordinates.couplingAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.couplingAssembly.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn,
  GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_2 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_2,
  GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_3 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_3,
  GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_4 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_4,
  GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_5 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_5,
  GUT.HeeckLeSixQuarkPairCoordinates.coupling_split => Physics.HeeckLeSixQuarkPairCoordinates.coupling_split,
  GUT.HeeckLeSixQuarkPairCoordinates.evenAssembly => Physics.HeeckLeSixQuarkPairCoordinates.evenAssembly,
  GUT.HeeckLeSixQuarkPairCoordinates.evenAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.evenAssembly.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.evenColumn => Physics.HeeckLeSixQuarkPairCoordinates.evenColumn,
  GUT.HeeckLeSixQuarkPairCoordinates.evenColumn.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.evenColumn.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.evenSelect => Physics.HeeckLeSixQuarkPairCoordinates.evenSelect,
  GUT.HeeckLeSixQuarkPairCoordinates.evenSelect.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.evenSelect.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.joinZero => Physics.HeeckLeSixQuarkPairCoordinates.joinZero,
  GUT.HeeckLeSixQuarkPairCoordinates.joinZero.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.joinZero.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.joinZeroLinear => Physics.HeeckLeSixQuarkPairCoordinates.joinZeroLinear,
  GUT.HeeckLeSixQuarkPairCoordinates.join_select => Physics.HeeckLeSixQuarkPairCoordinates.join_select,
  GUT.HeeckLeSixQuarkPairCoordinates.leftAssembly => Physics.HeeckLeSixQuarkPairCoordinates.leftAssembly,
  GUT.HeeckLeSixQuarkPairCoordinates.leftAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftAssembly.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.leftIndex => Physics.HeeckLeSixQuarkPairCoordinates.leftIndex,
  GUT.HeeckLeSixQuarkPairCoordinates.leftIndex.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftIndex.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.leftOfCoupling => Physics.HeeckLeSixQuarkPairCoordinates.leftOfCoupling,
  GUT.HeeckLeSixQuarkPairCoordinates.leftOfCoupling.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftOfCoupling.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.leftSelect => Physics.HeeckLeSixQuarkPairCoordinates.leftSelect,
  GUT.HeeckLeSixQuarkPairCoordinates.leftSelect.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftSelect.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.oddAssembly => Physics.HeeckLeSixQuarkPairCoordinates.oddAssembly,
  GUT.HeeckLeSixQuarkPairCoordinates.oddAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.oddAssembly.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.oddColumn => Physics.HeeckLeSixQuarkPairCoordinates.oddColumn,
  GUT.HeeckLeSixQuarkPairCoordinates.oddColumn.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.oddColumn.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.oddSelect => Physics.HeeckLeSixQuarkPairCoordinates.oddSelect,
  GUT.HeeckLeSixQuarkPairCoordinates.oddSelect.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.oddSelect.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.pairLeft => Physics.HeeckLeSixQuarkPairCoordinates.pairLeft,
  GUT.HeeckLeSixQuarkPairCoordinates.pairLeft.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.pairLeft.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.pairRight => Physics.HeeckLeSixQuarkPairCoordinates.pairRight,
  GUT.HeeckLeSixQuarkPairCoordinates.pairRight.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.pairRight.eq_1,
  GUT.HeeckLeSixQuarkPairCoordinates.source0_split => Physics.HeeckLeSixQuarkPairCoordinates.source0_split
]

assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingAssembly => Physics.HeeckLeSixQuarkPairCoordinates.couplingAssembly
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.couplingAssembly.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_2 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_2
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_3 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_3
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_4 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_4
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_5 => Physics.HeeckLeSixQuarkPairCoordinates.couplingColumn.eq_5
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.coupling_split => Physics.HeeckLeSixQuarkPairCoordinates.coupling_split
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.evenAssembly => Physics.HeeckLeSixQuarkPairCoordinates.evenAssembly
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.evenAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.evenAssembly.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.evenColumn => Physics.HeeckLeSixQuarkPairCoordinates.evenColumn
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.evenColumn.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.evenColumn.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.evenSelect => Physics.HeeckLeSixQuarkPairCoordinates.evenSelect
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.evenSelect.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.evenSelect.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.joinZero => Physics.HeeckLeSixQuarkPairCoordinates.joinZero
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.joinZero.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.joinZero.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.joinZeroLinear => Physics.HeeckLeSixQuarkPairCoordinates.joinZeroLinear
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.join_select => Physics.HeeckLeSixQuarkPairCoordinates.join_select
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftAssembly => Physics.HeeckLeSixQuarkPairCoordinates.leftAssembly
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftAssembly.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftIndex => Physics.HeeckLeSixQuarkPairCoordinates.leftIndex
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftIndex.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftIndex.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftOfCoupling => Physics.HeeckLeSixQuarkPairCoordinates.leftOfCoupling
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftOfCoupling.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftOfCoupling.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftSelect => Physics.HeeckLeSixQuarkPairCoordinates.leftSelect
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.leftSelect.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.leftSelect.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.oddAssembly => Physics.HeeckLeSixQuarkPairCoordinates.oddAssembly
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.oddAssembly.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.oddAssembly.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.oddColumn => Physics.HeeckLeSixQuarkPairCoordinates.oddColumn
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.oddColumn.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.oddColumn.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.oddSelect => Physics.HeeckLeSixQuarkPairCoordinates.oddSelect
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.oddSelect.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.oddSelect.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.pairLeft => Physics.HeeckLeSixQuarkPairCoordinates.pairLeft
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.pairLeft.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.pairLeft.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.pairRight => Physics.HeeckLeSixQuarkPairCoordinates.pairRight
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.pairRight.eq_1 => Physics.HeeckLeSixQuarkPairCoordinates.pairRight.eq_1
assert_compatible GUT.HeeckLeSixQuarkPairCoordinates.source0_split => Physics.HeeckLeSixQuarkPairCoordinates.source0_split
