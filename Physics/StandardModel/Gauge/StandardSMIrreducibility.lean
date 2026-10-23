import Physics.StandardModel.Gauge.Tensors.StandardSMIrreducibility
import Physics.StandardModel.Gauge.StandardSMGaugeTensor
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.StandardSMIrreducibility instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StandardSMIrreducibility.electronLeft_irreducible => Physics.StandardSMIrreducibility.electronLeft_irreducible,
  GUT.StandardSMIrreducibility.electronRight_irreducible => Physics.StandardSMIrreducibility.electronRight_irreducible,
  GUT.StandardSMIrreducibility.quark_irreducible => Physics.StandardSMIrreducibility.quark_irreducible,
  GUT.StandardSMIrreducibility.upLeft_irreducible => Physics.StandardSMIrreducibility.upLeft_irreducible,
  GUT.StandardSMIrreducibility.upRight_irreducible => Physics.StandardSMIrreducibility.upRight_irreducible
]

assert_compatible GUT.StandardSMIrreducibility.electronLeft_irreducible => Physics.StandardSMIrreducibility.electronLeft_irreducible
assert_compatible GUT.StandardSMIrreducibility.electronRight_irreducible => Physics.StandardSMIrreducibility.electronRight_irreducible
assert_compatible GUT.StandardSMIrreducibility.quark_irreducible => Physics.StandardSMIrreducibility.quark_irreducible
assert_compatible GUT.StandardSMIrreducibility.upLeft_irreducible => Physics.StandardSMIrreducibility.upLeft_irreducible
assert_compatible GUT.StandardSMIrreducibility.upRight_irreducible => Physics.StandardSMIrreducibility.upRight_irreducible
