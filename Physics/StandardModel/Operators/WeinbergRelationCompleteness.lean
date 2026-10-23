import Physics.StandardModel.Operators.Weinberg.WeinbergRelationCompleteness
import Physics.StandardModel.Operators.WeinbergPermutationCompleteness
import Physics.StandardModel.Operators.WeinbergModelSector
import Math.RepresentationTheory.FiniteLocalRelationCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Weinberg.WeinbergRelationCompleteness instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeinbergRelationCompleteness.complete => Physics.WeinbergRelationCompleteness.complete,
  GUT.WeinbergRelationCompleteness.contractions => Physics.WeinbergRelationCompleteness.contractions,
  GUT.WeinbergRelationCompleteness.contractions.eq_1 => Physics.WeinbergRelationCompleteness.contractions.eq_1,
  GUT.WeinbergRelationCompleteness.equiv => Physics.WeinbergRelationCompleteness.equiv,
  GUT.WeinbergRelationCompleteness.extraction => Physics.WeinbergRelationCompleteness.extraction,
  GUT.WeinbergRelationCompleteness.flavorExchange => Physics.WeinbergRelationCompleteness.flavorExchange,
  GUT.WeinbergRelationCompleteness.generatorEquiv => Physics.WeinbergRelationCompleteness.generatorEquiv,
  GUT.WeinbergRelationCompleteness.localExchange => Physics.WeinbergRelationCompleteness.localExchange,
  GUT.WeinbergRelationCompleteness.modelEquiv => Physics.WeinbergRelationCompleteness.modelEquiv,
  GUT.WeinbergRelationCompleteness.modelEquiv_agrees => Physics.WeinbergRelationCompleteness.modelEquiv_agrees,
  GUT.WeinbergRelationCompleteness.normalized => Physics.WeinbergRelationCompleteness.normalized,
  GUT.WeinbergRelationCompleteness.probes => Physics.WeinbergRelationCompleteness.probes,
  GUT.WeinbergRelationCompleteness.probes.eq_1 => Physics.WeinbergRelationCompleteness.probes.eq_1,
  GUT.WeinbergRelationCompleteness.relations => Physics.WeinbergRelationCompleteness.relations,
  GUT.WeinbergRelationCompleteness.residualRepresentation => Physics.WeinbergRelationCompleteness.residualRepresentation,
  GUT.WeinbergRelationCompleteness.sign => Physics.WeinbergRelationCompleteness.sign,
  GUT.WeinbergRelationCompleteness.symmetricHomEquiv => Physics.WeinbergRelationCompleteness.symmetricHomEquiv,
  GUT.WeinbergRelationCompleteness.symmetricHomEquiv.eq_1 => Physics.WeinbergRelationCompleteness.symmetricHomEquiv.eq_1,
  GUT.WeinbergRelationCompleteness.symmetricHomEquiv_agrees => Physics.WeinbergRelationCompleteness.symmetricHomEquiv_agrees
]

assert_compatible GUT.WeinbergRelationCompleteness.complete => Physics.WeinbergRelationCompleteness.complete
assert_compatible GUT.WeinbergRelationCompleteness.contractions => Physics.WeinbergRelationCompleteness.contractions
assert_compatible GUT.WeinbergRelationCompleteness.contractions.eq_1 => Physics.WeinbergRelationCompleteness.contractions.eq_1
assert_compatible GUT.WeinbergRelationCompleteness.equiv => Physics.WeinbergRelationCompleteness.equiv
assert_compatible GUT.WeinbergRelationCompleteness.extraction => Physics.WeinbergRelationCompleteness.extraction
assert_compatible GUT.WeinbergRelationCompleteness.flavorExchange => Physics.WeinbergRelationCompleteness.flavorExchange
assert_compatible GUT.WeinbergRelationCompleteness.generatorEquiv => Physics.WeinbergRelationCompleteness.generatorEquiv
assert_compatible GUT.WeinbergRelationCompleteness.localExchange => Physics.WeinbergRelationCompleteness.localExchange
assert_compatible GUT.WeinbergRelationCompleteness.modelEquiv => Physics.WeinbergRelationCompleteness.modelEquiv
assert_compatible GUT.WeinbergRelationCompleteness.modelEquiv_agrees => Physics.WeinbergRelationCompleteness.modelEquiv_agrees
assert_compatible GUT.WeinbergRelationCompleteness.normalized => Physics.WeinbergRelationCompleteness.normalized
assert_compatible GUT.WeinbergRelationCompleteness.probes => Physics.WeinbergRelationCompleteness.probes
assert_compatible GUT.WeinbergRelationCompleteness.probes.eq_1 => Physics.WeinbergRelationCompleteness.probes.eq_1
assert_compatible GUT.WeinbergRelationCompleteness.relations => Physics.WeinbergRelationCompleteness.relations
assert_compatible GUT.WeinbergRelationCompleteness.residualRepresentation => Physics.WeinbergRelationCompleteness.residualRepresentation
assert_compatible GUT.WeinbergRelationCompleteness.sign => Physics.WeinbergRelationCompleteness.sign
assert_compatible GUT.WeinbergRelationCompleteness.symmetricHomEquiv => Physics.WeinbergRelationCompleteness.symmetricHomEquiv
assert_compatible GUT.WeinbergRelationCompleteness.symmetricHomEquiv.eq_1 => Physics.WeinbergRelationCompleteness.symmetricHomEquiv.eq_1
assert_compatible GUT.WeinbergRelationCompleteness.symmetricHomEquiv_agrees => Physics.WeinbergRelationCompleteness.symmetricHomEquiv_agrees
