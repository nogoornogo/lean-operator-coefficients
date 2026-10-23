import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraParity
import Physics.StandardModel.Operators.ComposableBLSupport
import Physics.StandardModel.Operators.WeinbergSMInterface
import Math.LinearAlgebra.MixedSelectionRequests
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraParity instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraParity.H => Physics.DevMohapatraParity.H,
  GUT.DevMohapatraParity.LLHH => Physics.DevMohapatraParity.LLHH,
  GUT.DevMohapatraParity.all_bOne_forbidden => Physics.DevMohapatraParity.all_bOne_forbidden,
  GUT.DevMohapatraParity.chi => Physics.DevMohapatraParity.chi,
  GUT.DevMohapatraParity.chi.eq_1 => Physics.DevMohapatraParity.chi.eq_1,
  GUT.DevMohapatraParity.copies => Physics.DevMohapatraParity.copies,
  GUT.DevMohapatraParity.copies.eq_1 => Physics.DevMohapatraParity.copies.eq_1,
  GUT.DevMohapatraParity.detect => Physics.DevMohapatraParity.detect,
  GUT.DevMohapatraParity.flavor => Physics.DevMohapatraParity.flavor,
  GUT.DevMohapatraParity.flavor.eq_1 => Physics.DevMohapatraParity.flavor.eq_1,
  GUT.DevMohapatraParity.higgs_trivial => Physics.DevMohapatraParity.higgs_trivial,
  GUT.DevMohapatraParity.lepton_trivial => Physics.DevMohapatraParity.lepton_trivial,
  GUT.DevMohapatraParity.llhh_allowed => Physics.DevMohapatraParity.llhh_allowed,
  GUT.DevMohapatraParity.scalarFlavor => Physics.DevMohapatraParity.scalarFlavor,
  GUT.DevMohapatraParity.scalarFlavor.eq_1 => Physics.DevMohapatraParity.scalarFlavor.eq_1
]

assert_compatible GUT.DevMohapatraParity.H => Physics.DevMohapatraParity.H
assert_compatible GUT.DevMohapatraParity.LLHH => Physics.DevMohapatraParity.LLHH
assert_compatible GUT.DevMohapatraParity.all_bOne_forbidden => Physics.DevMohapatraParity.all_bOne_forbidden
assert_compatible GUT.DevMohapatraParity.chi => Physics.DevMohapatraParity.chi
assert_compatible GUT.DevMohapatraParity.chi.eq_1 => Physics.DevMohapatraParity.chi.eq_1
assert_compatible GUT.DevMohapatraParity.copies => Physics.DevMohapatraParity.copies
assert_compatible GUT.DevMohapatraParity.copies.eq_1 => Physics.DevMohapatraParity.copies.eq_1
assert_compatible GUT.DevMohapatraParity.detect => Physics.DevMohapatraParity.detect
assert_compatible GUT.DevMohapatraParity.flavor => Physics.DevMohapatraParity.flavor
assert_compatible GUT.DevMohapatraParity.flavor.eq_1 => Physics.DevMohapatraParity.flavor.eq_1
assert_compatible GUT.DevMohapatraParity.higgs_trivial => Physics.DevMohapatraParity.higgs_trivial
assert_compatible GUT.DevMohapatraParity.lepton_trivial => Physics.DevMohapatraParity.lepton_trivial
assert_compatible GUT.DevMohapatraParity.llhh_allowed => Physics.DevMohapatraParity.llhh_allowed
assert_compatible GUT.DevMohapatraParity.scalarFlavor => Physics.DevMohapatraParity.scalarFlavor
assert_compatible GUT.DevMohapatraParity.scalarFlavor.eq_1 => Physics.DevMohapatraParity.scalarFlavor.eq_1
