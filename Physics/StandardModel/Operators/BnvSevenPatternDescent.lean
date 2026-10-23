import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenPatternDescent
import Physics.StandardModel.Operators.BnvMixedWeylSupport
import Math.RepresentationTheory.MixedSinglePatternAssembly
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenPatternDescent instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenPatternDescent.equiv => Physics.BnvSevenPatternDescent.equiv,
  GUT.BnvSevenPatternDescent.family => Physics.BnvSevenPatternDescent.family,
  GUT.BnvSevenPatternDescent.family_bnv => Physics.BnvSevenPatternDescent.family_bnv,
  GUT.BnvSevenPatternDescent.ordered => Physics.BnvSevenPatternDescent.ordered,
  GUT.BnvSevenPatternDescent.pattern => Physics.BnvSevenPatternDescent.pattern,
  GUT.BnvSevenPatternDescent.pattern.eq_1 => Physics.BnvSevenPatternDescent.pattern.eq_1,
  GUT.BnvSevenPatternDescent.pattern.eq_2 => Physics.BnvSevenPatternDescent.pattern.eq_2,
  GUT.BnvSevenPatternDescent.pattern.eq_3 => Physics.BnvSevenPatternDescent.pattern.eq_3,
  GUT.BnvSevenPatternDescent.pattern.eq_4 => Physics.BnvSevenPatternDescent.pattern.eq_4,
  GUT.BnvSevenPatternDescent.pattern_baryon => Physics.BnvSevenPatternDescent.pattern_baryon,
  GUT.BnvSevenPatternDescent.pattern_counts => Physics.BnvSevenPatternDescent.pattern_counts,
  GUT.BnvSevenPatternDescent.pattern_hypercharge => Physics.BnvSevenPatternDescent.pattern_hypercharge,
  GUT.BnvSevenPatternDescent.scalar => Physics.BnvSevenPatternDescent.scalar,
  GUT.BnvSevenPatternDescent.scalar.eq_1 => Physics.BnvSevenPatternDescent.scalar.eq_1
]

assert_compatible GUT.BnvSevenPatternDescent.equiv => Physics.BnvSevenPatternDescent.equiv
assert_compatible GUT.BnvSevenPatternDescent.family => Physics.BnvSevenPatternDescent.family
assert_compatible GUT.BnvSevenPatternDescent.family_bnv => Physics.BnvSevenPatternDescent.family_bnv
assert_compatible GUT.BnvSevenPatternDescent.ordered => Physics.BnvSevenPatternDescent.ordered
assert_compatible GUT.BnvSevenPatternDescent.pattern => Physics.BnvSevenPatternDescent.pattern
assert_compatible GUT.BnvSevenPatternDescent.pattern.eq_1 => Physics.BnvSevenPatternDescent.pattern.eq_1
assert_compatible GUT.BnvSevenPatternDescent.pattern.eq_2 => Physics.BnvSevenPatternDescent.pattern.eq_2
assert_compatible GUT.BnvSevenPatternDescent.pattern.eq_3 => Physics.BnvSevenPatternDescent.pattern.eq_3
assert_compatible GUT.BnvSevenPatternDescent.pattern.eq_4 => Physics.BnvSevenPatternDescent.pattern.eq_4
assert_compatible GUT.BnvSevenPatternDescent.pattern_baryon => Physics.BnvSevenPatternDescent.pattern_baryon
assert_compatible GUT.BnvSevenPatternDescent.pattern_counts => Physics.BnvSevenPatternDescent.pattern_counts
assert_compatible GUT.BnvSevenPatternDescent.pattern_hypercharge => Physics.BnvSevenPatternDescent.pattern_hypercharge
assert_compatible GUT.BnvSevenPatternDescent.scalar => Physics.BnvSevenPatternDescent.scalar
assert_compatible GUT.BnvSevenPatternDescent.scalar.eq_1 => Physics.BnvSevenPatternDescent.scalar.eq_1
