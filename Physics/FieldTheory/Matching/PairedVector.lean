import Physics.FieldTheory.Matching.Core.PairedVector
import Math.LinearAlgebra.PairedQuadraticElimination
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Matching.Core.PairedVector instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.PairedVector.Vector => Physics.PairedVector.Vector,
  GUT.PairedVector.eliminate => Physics.PairedVector.eliminate,
  GUT.PairedVector.pair => Physics.PairedVector.pair,
  GUT.PairedVector.pair.eq_1 => Physics.PairedVector.pair.eq_1,
  GUT.PairedVector.pairing => Physics.PairedVector.pairing,
  GUT.PairedVector.pairing_nondegenerate => Physics.PairedVector.pairing_nondegenerate,
  GUT.PairedVector.pairing_rankOne => Physics.PairedVector.pairing_rankOne,
  GUT.PairedVector.pairing_symmetric => Physics.PairedVector.pairing_symmetric,
  GUT.PairedVector.rankOne => Physics.PairedVector.rankOne,
  GUT.PairedVector.rankOne.eq_1 => Physics.PairedVector.rankOne.eq_1
]

assert_compatible GUT.PairedVector.Vector => Physics.PairedVector.Vector
assert_compatible GUT.PairedVector.eliminate => Physics.PairedVector.eliminate
assert_compatible GUT.PairedVector.pair => Physics.PairedVector.pair
assert_compatible GUT.PairedVector.pair.eq_1 => Physics.PairedVector.pair.eq_1
assert_compatible GUT.PairedVector.pairing => Physics.PairedVector.pairing
assert_compatible GUT.PairedVector.pairing_nondegenerate => Physics.PairedVector.pairing_nondegenerate
assert_compatible GUT.PairedVector.pairing_rankOne => Physics.PairedVector.pairing_rankOne
assert_compatible GUT.PairedVector.pairing_symmetric => Physics.PairedVector.pairing_symmetric
assert_compatible GUT.PairedVector.rankOne => Physics.PairedVector.rankOne
assert_compatible GUT.PairedVector.rankOne.eq_1 => Physics.PairedVector.rankOne.eq_1
