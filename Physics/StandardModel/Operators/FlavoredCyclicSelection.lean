import Physics.StandardModel.Operators.Selection.FlavoredCyclicSelection
import Physics.StandardModel.Operators.FlavoredCyclicCoordinates
import Physics.StandardModel.Operators.QqqlDiagonalCoordinates
import Physics.StandardModel.Operators.DeltaLOneCoefficientCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.FlavoredCyclicSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavoredCyclicSelection.Coordinates => Physics.FlavoredCyclicSelection.Coordinates,
  GUT.FlavoredCyclicSelection.DuqlIndex => Physics.FlavoredCyclicSelection.DuqlIndex,
  GUT.FlavoredCyclicSelection.DuueIndex => Physics.FlavoredCyclicSelection.DuueIndex,
  GUT.FlavoredCyclicSelection.QqqlIndex => Physics.FlavoredCyclicSelection.QqqlIndex,
  GUT.FlavoredCyclicSelection.QqueIndex => Physics.FlavoredCyclicSelection.QqueIndex,
  GUT.FlavoredCyclicSelection.allowed_function => Physics.FlavoredCyclicSelection.allowed_function,
  GUT.FlavoredCyclicSelection.allowed_total_iff => Physics.FlavoredCyclicSelection.allowed_total_iff,
  GUT.FlavoredCyclicSelection.duqlResidualEquiv => Physics.FlavoredCyclicSelection.duqlResidualEquiv,
  GUT.FlavoredCyclicSelection.duueResidualEquiv => Physics.FlavoredCyclicSelection.duueResidualEquiv,
  GUT.FlavoredCyclicSelection.equiv => Physics.FlavoredCyclicSelection.equiv,
  GUT.FlavoredCyclicSelection.extract_reconstruct => Physics.FlavoredCyclicSelection.extract_reconstruct,
  GUT.FlavoredCyclicSelection.finrank_total => Physics.FlavoredCyclicSelection.finrank_total,
  GUT.FlavoredCyclicSelection.flavor => Physics.FlavoredCyclicSelection.flavor,
  GUT.FlavoredCyclicSelection.forbidden_function => Physics.FlavoredCyclicSelection.forbidden_function,
  GUT.FlavoredCyclicSelection.forbidden_total_iff => Physics.FlavoredCyclicSelection.forbidden_total_iff,
  GUT.FlavoredCyclicSelection.opposite_charge => Physics.FlavoredCyclicSelection.opposite_charge,
  GUT.FlavoredCyclicSelection.opposite_slot => Physics.FlavoredCyclicSelection.opposite_slot,
  GUT.FlavoredCyclicSelection.qqqlResidualEquiv => Physics.FlavoredCyclicSelection.qqqlResidualEquiv,
  GUT.FlavoredCyclicSelection.qqueResidualEquiv => Physics.FlavoredCyclicSelection.qqueResidualEquiv,
  GUT.FlavoredCyclicSelection.reconstruct_extract => Physics.FlavoredCyclicSelection.reconstruct_extract,
  GUT.FlavoredCyclicSelection.signedCharge => Physics.FlavoredCyclicSelection.signedCharge,
  GUT.FlavoredCyclicSelection.signedCharge.eq_1 => Physics.FlavoredCyclicSelection.signedCharge.eq_1,
  GUT.FlavoredCyclicSelection.signedIndex => Physics.FlavoredCyclicSelection.signedIndex,
  GUT.FlavoredCyclicSelection.simultaneous_iff => Physics.FlavoredCyclicSelection.simultaneous_iff,
  GUT.FlavoredCyclicSelection.slot => Physics.FlavoredCyclicSelection.slot,
  GUT.FlavoredCyclicSelection.slot.eq_1 => Physics.FlavoredCyclicSelection.slot.eq_1
]

assert_compatible GUT.FlavoredCyclicSelection.Coordinates => Physics.FlavoredCyclicSelection.Coordinates
assert_compatible GUT.FlavoredCyclicSelection.DuqlIndex => Physics.FlavoredCyclicSelection.DuqlIndex
assert_compatible GUT.FlavoredCyclicSelection.DuueIndex => Physics.FlavoredCyclicSelection.DuueIndex
assert_compatible GUT.FlavoredCyclicSelection.QqqlIndex => Physics.FlavoredCyclicSelection.QqqlIndex
assert_compatible GUT.FlavoredCyclicSelection.QqueIndex => Physics.FlavoredCyclicSelection.QqueIndex
assert_compatible GUT.FlavoredCyclicSelection.allowed_function => Physics.FlavoredCyclicSelection.allowed_function
assert_compatible GUT.FlavoredCyclicSelection.allowed_total_iff => Physics.FlavoredCyclicSelection.allowed_total_iff
assert_compatible GUT.FlavoredCyclicSelection.duqlResidualEquiv => Physics.FlavoredCyclicSelection.duqlResidualEquiv
assert_compatible GUT.FlavoredCyclicSelection.duueResidualEquiv => Physics.FlavoredCyclicSelection.duueResidualEquiv
assert_compatible GUT.FlavoredCyclicSelection.equiv => Physics.FlavoredCyclicSelection.equiv
assert_compatible GUT.FlavoredCyclicSelection.extract_reconstruct => Physics.FlavoredCyclicSelection.extract_reconstruct
assert_compatible GUT.FlavoredCyclicSelection.finrank_total => Physics.FlavoredCyclicSelection.finrank_total
assert_compatible GUT.FlavoredCyclicSelection.flavor => Physics.FlavoredCyclicSelection.flavor
assert_compatible GUT.FlavoredCyclicSelection.forbidden_function => Physics.FlavoredCyclicSelection.forbidden_function
assert_compatible GUT.FlavoredCyclicSelection.forbidden_total_iff => Physics.FlavoredCyclicSelection.forbidden_total_iff
assert_compatible GUT.FlavoredCyclicSelection.opposite_charge => Physics.FlavoredCyclicSelection.opposite_charge
assert_compatible GUT.FlavoredCyclicSelection.opposite_slot => Physics.FlavoredCyclicSelection.opposite_slot
assert_compatible GUT.FlavoredCyclicSelection.qqqlResidualEquiv => Physics.FlavoredCyclicSelection.qqqlResidualEquiv
assert_compatible GUT.FlavoredCyclicSelection.qqueResidualEquiv => Physics.FlavoredCyclicSelection.qqueResidualEquiv
assert_compatible GUT.FlavoredCyclicSelection.reconstruct_extract => Physics.FlavoredCyclicSelection.reconstruct_extract
assert_compatible GUT.FlavoredCyclicSelection.signedCharge => Physics.FlavoredCyclicSelection.signedCharge
assert_compatible GUT.FlavoredCyclicSelection.signedCharge.eq_1 => Physics.FlavoredCyclicSelection.signedCharge.eq_1
assert_compatible GUT.FlavoredCyclicSelection.signedIndex => Physics.FlavoredCyclicSelection.signedIndex
assert_compatible GUT.FlavoredCyclicSelection.simultaneous_iff => Physics.FlavoredCyclicSelection.simultaneous_iff
assert_compatible GUT.FlavoredCyclicSelection.slot => Physics.FlavoredCyclicSelection.slot
assert_compatible GUT.FlavoredCyclicSelection.slot.eq_1 => Physics.FlavoredCyclicSelection.slot.eq_1
