import Physics.FieldTheory.Spinor.Weyl.DistinctFermionCoefficient
import Math.LinearAlgebra.DistinctSpeciesBilinear
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.DistinctFermionCoefficient instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DistinctFermionCoefficient.alternating => Physics.DistinctFermionCoefficient.alternating,
  GUT.DistinctFermionCoefficient.extension => Physics.DistinctFermionCoefficient.extension,
  GUT.DistinctFermionCoefficient.extension.eq_1 => Physics.DistinctFermionCoefficient.extension.eq_1,
  GUT.DistinctFermionCoefficient.extension_injective => Physics.DistinctFermionCoefficient.extension_injective,
  GUT.DistinctFermionCoefficient.ordered => Physics.DistinctFermionCoefficient.ordered,
  GUT.DistinctFermionCoefficient.restriction => Physics.DistinctFermionCoefficient.restriction
]

assert_compatible GUT.DistinctFermionCoefficient.alternating => Physics.DistinctFermionCoefficient.alternating
assert_compatible GUT.DistinctFermionCoefficient.extension => Physics.DistinctFermionCoefficient.extension
assert_compatible GUT.DistinctFermionCoefficient.extension.eq_1 => Physics.DistinctFermionCoefficient.extension.eq_1
assert_compatible GUT.DistinctFermionCoefficient.extension_injective => Physics.DistinctFermionCoefficient.extension_injective
assert_compatible GUT.DistinctFermionCoefficient.ordered => Physics.DistinctFermionCoefficient.ordered
assert_compatible GUT.DistinctFermionCoefficient.restriction => Physics.DistinctFermionCoefficient.restriction
