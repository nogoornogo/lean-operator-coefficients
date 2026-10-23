import Physics.StandardModel.Operators.Selection.InverseCyclicSMYukawa
import Physics.StandardModel.Spectrum.InverseCyclicSMRealization
import Physics.StandardModel.Gauge.SMYukawaContractions
import Physics.FieldTheory.Yukawa.SpinorYukawaContraction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.InverseCyclicSMYukawa instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.InverseCyclicSMYukawa.antiHiggs => Physics.InverseCyclicSMYukawa.antiHiggs,
  GUT.InverseCyclicSMYukawa.construction_certificate => Physics.InverseCyclicSMYukawa.construction_certificate,
  GUT.InverseCyclicSMYukawa.copy => Physics.InverseCyclicSMYukawa.copy,
  GUT.InverseCyclicSMYukawa.down => Physics.InverseCyclicSMYukawa.down,
  GUT.InverseCyclicSMYukawa.downInternal => Physics.InverseCyclicSMYukawa.downInternal,
  GUT.InverseCyclicSMYukawa.down_nonzero => Physics.InverseCyclicSMYukawa.down_nonzero,
  GUT.InverseCyclicSMYukawa.electron => Physics.InverseCyclicSMYukawa.electron,
  GUT.InverseCyclicSMYukawa.electronInternal => Physics.InverseCyclicSMYukawa.electronInternal,
  GUT.InverseCyclicSMYukawa.electron_nonzero => Physics.InverseCyclicSMYukawa.electron_nonzero,
  GUT.InverseCyclicSMYukawa.firstFlavor => Physics.InverseCyclicSMYukawa.firstFlavor,
  GUT.InverseCyclicSMYukawa.flavorLinear => Physics.InverseCyclicSMYukawa.flavorLinear,
  GUT.InverseCyclicSMYukawa.flavorLinear.eq_1 => Physics.InverseCyclicSMYukawa.flavorLinear.eq_1,
  GUT.InverseCyclicSMYukawa.flavorLinear_apply => Physics.InverseCyclicSMYukawa.flavorLinear_apply,
  GUT.InverseCyclicSMYukawa.flavorPair => Physics.InverseCyclicSMYukawa.flavorPair,
  GUT.InverseCyclicSMYukawa.flavorPair.eq_1 => Physics.InverseCyclicSMYukawa.flavorPair.eq_1,
  GUT.InverseCyclicSMYukawa.flavorTriple => Physics.InverseCyclicSMYukawa.flavorTriple,
  GUT.InverseCyclicSMYukawa.flavorTriple.eq_1 => Physics.InverseCyclicSMYukawa.flavorTriple.eq_1,
  GUT.InverseCyclicSMYukawa.higgs => Physics.InverseCyclicSMYukawa.higgs,
  GUT.InverseCyclicSMYukawa.internal => Physics.InverseCyclicSMYukawa.internal,
  GUT.InverseCyclicSMYukawa.internal.eq_1 => Physics.InverseCyclicSMYukawa.internal.eq_1,
  GUT.InverseCyclicSMYukawa.internal_apply => Physics.InverseCyclicSMYukawa.internal_apply,
  GUT.InverseCyclicSMYukawa.regroup => Physics.InverseCyclicSMYukawa.regroup,
  GUT.InverseCyclicSMYukawa.regroup.eq_1 => Physics.InverseCyclicSMYukawa.regroup.eq_1,
  GUT.InverseCyclicSMYukawa.scalarCopy => Physics.InverseCyclicSMYukawa.scalarCopy,
  GUT.InverseCyclicSMYukawa.up => Physics.InverseCyclicSMYukawa.up,
  GUT.InverseCyclicSMYukawa.upInternal => Physics.InverseCyclicSMYukawa.upInternal,
  GUT.InverseCyclicSMYukawa.up_nonzero => Physics.InverseCyclicSMYukawa.up_nonzero
]

assert_compatible GUT.InverseCyclicSMYukawa.antiHiggs => Physics.InverseCyclicSMYukawa.antiHiggs
assert_compatible GUT.InverseCyclicSMYukawa.construction_certificate => Physics.InverseCyclicSMYukawa.construction_certificate
assert_compatible GUT.InverseCyclicSMYukawa.copy => Physics.InverseCyclicSMYukawa.copy
assert_compatible GUT.InverseCyclicSMYukawa.down => Physics.InverseCyclicSMYukawa.down
assert_compatible GUT.InverseCyclicSMYukawa.downInternal => Physics.InverseCyclicSMYukawa.downInternal
assert_compatible GUT.InverseCyclicSMYukawa.down_nonzero => Physics.InverseCyclicSMYukawa.down_nonzero
assert_compatible GUT.InverseCyclicSMYukawa.electron => Physics.InverseCyclicSMYukawa.electron
assert_compatible GUT.InverseCyclicSMYukawa.electronInternal => Physics.InverseCyclicSMYukawa.electronInternal
assert_compatible GUT.InverseCyclicSMYukawa.electron_nonzero => Physics.InverseCyclicSMYukawa.electron_nonzero
assert_compatible GUT.InverseCyclicSMYukawa.firstFlavor => Physics.InverseCyclicSMYukawa.firstFlavor
assert_compatible GUT.InverseCyclicSMYukawa.flavorLinear => Physics.InverseCyclicSMYukawa.flavorLinear
assert_compatible GUT.InverseCyclicSMYukawa.flavorLinear.eq_1 => Physics.InverseCyclicSMYukawa.flavorLinear.eq_1
assert_compatible GUT.InverseCyclicSMYukawa.flavorLinear_apply => Physics.InverseCyclicSMYukawa.flavorLinear_apply
assert_compatible GUT.InverseCyclicSMYukawa.flavorPair => Physics.InverseCyclicSMYukawa.flavorPair
assert_compatible GUT.InverseCyclicSMYukawa.flavorPair.eq_1 => Physics.InverseCyclicSMYukawa.flavorPair.eq_1
assert_compatible GUT.InverseCyclicSMYukawa.flavorTriple => Physics.InverseCyclicSMYukawa.flavorTriple
assert_compatible GUT.InverseCyclicSMYukawa.flavorTriple.eq_1 => Physics.InverseCyclicSMYukawa.flavorTriple.eq_1
assert_compatible GUT.InverseCyclicSMYukawa.higgs => Physics.InverseCyclicSMYukawa.higgs
assert_compatible GUT.InverseCyclicSMYukawa.internal => Physics.InverseCyclicSMYukawa.internal
assert_compatible GUT.InverseCyclicSMYukawa.internal.eq_1 => Physics.InverseCyclicSMYukawa.internal.eq_1
assert_compatible GUT.InverseCyclicSMYukawa.internal_apply => Physics.InverseCyclicSMYukawa.internal_apply
assert_compatible GUT.InverseCyclicSMYukawa.regroup => Physics.InverseCyclicSMYukawa.regroup
assert_compatible GUT.InverseCyclicSMYukawa.regroup.eq_1 => Physics.InverseCyclicSMYukawa.regroup.eq_1
assert_compatible GUT.InverseCyclicSMYukawa.scalarCopy => Physics.InverseCyclicSMYukawa.scalarCopy
assert_compatible GUT.InverseCyclicSMYukawa.up => Physics.InverseCyclicSMYukawa.up
assert_compatible GUT.InverseCyclicSMYukawa.upInternal => Physics.InverseCyclicSMYukawa.upInternal
assert_compatible GUT.InverseCyclicSMYukawa.up_nonzero => Physics.InverseCyclicSMYukawa.up_nonzero
