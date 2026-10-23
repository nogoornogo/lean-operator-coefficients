import Physics.FieldTheory.Mass.Algebra.OrthogonalMass
import Physics.FieldTheory.Mass.ScaledMassSpectrum
import Physics.FieldTheory.Mass.LightInheritanceBoundary
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.OrthogonalMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.OrthogonalMass.finrank_prod => Physics.OrthogonalMass.finrank_prod,
  GUT.OrthogonalMass.mem_radical => Physics.OrthogonalMass.mem_radical,
  GUT.OrthogonalMass.pair => Physics.OrthogonalMass.pair,
  GUT.OrthogonalMass.pair.eq_1 => Physics.OrthogonalMass.pair.eq_1,
  GUT.OrthogonalMass.pair_apply => Physics.OrthogonalMass.pair_apply,
  GUT.OrthogonalMass.pair_radical => Physics.OrthogonalMass.pair_radical,
  GUT.OrthogonalMass.prod => Physics.OrthogonalMass.prod,
  GUT.OrthogonalMass.prod.eq_1 => Physics.OrthogonalMass.prod.eq_1,
  GUT.OrthogonalMass.prod_apply => Physics.OrthogonalMass.prod_apply,
  GUT.OrthogonalMass.radicalEquiv => Physics.OrthogonalMass.radicalEquiv
]

assert_compatible GUT.OrthogonalMass.finrank_prod => Physics.OrthogonalMass.finrank_prod
assert_compatible GUT.OrthogonalMass.mem_radical => Physics.OrthogonalMass.mem_radical
assert_compatible GUT.OrthogonalMass.pair => Physics.OrthogonalMass.pair
assert_compatible GUT.OrthogonalMass.pair.eq_1 => Physics.OrthogonalMass.pair.eq_1
assert_compatible GUT.OrthogonalMass.pair_apply => Physics.OrthogonalMass.pair_apply
assert_compatible GUT.OrthogonalMass.pair_radical => Physics.OrthogonalMass.pair_radical
assert_compatible GUT.OrthogonalMass.prod => Physics.OrthogonalMass.prod
assert_compatible GUT.OrthogonalMass.prod.eq_1 => Physics.OrthogonalMass.prod.eq_1
assert_compatible GUT.OrthogonalMass.prod_apply => Physics.OrthogonalMass.prod_apply
assert_compatible GUT.OrthogonalMass.radicalEquiv => Physics.OrthogonalMass.radicalEquiv
