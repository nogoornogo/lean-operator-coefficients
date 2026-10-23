import Physics.FieldTheory.Yukawa.Mass.YukawaClassification
import Physics.FieldTheory.Yukawa.SymmetricScalarYukawa
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.YukawaClassification instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.YukawaClassification.endomorphismEquiv => Physics.YukawaClassification.endomorphismEquiv,
  GUT.YukawaClassification.equiv => Physics.YukawaClassification.equiv,
  GUT.YukawaClassification.evaluation => Physics.YukawaClassification.evaluation,
  GUT.YukawaClassification.ofMap => Physics.YukawaClassification.ofMap,
  GUT.YukawaClassification.ofMap_toMap => Physics.YukawaClassification.ofMap_toMap,
  GUT.YukawaClassification.scalarMultiple => Physics.YukawaClassification.scalarMultiple,
  GUT.YukawaClassification.scalarMultiple_apply => Physics.YukawaClassification.scalarMultiple_apply,
  GUT.YukawaClassification.toMap => Physics.YukawaClassification.toMap,
  GUT.YukawaClassification.toMap_ofMap => Physics.YukawaClassification.toMap_ofMap
]

assert_compatible GUT.YukawaClassification.endomorphismEquiv => Physics.YukawaClassification.endomorphismEquiv
assert_compatible GUT.YukawaClassification.equiv => Physics.YukawaClassification.equiv
assert_compatible GUT.YukawaClassification.evaluation => Physics.YukawaClassification.evaluation
assert_compatible GUT.YukawaClassification.ofMap => Physics.YukawaClassification.ofMap
assert_compatible GUT.YukawaClassification.ofMap_toMap => Physics.YukawaClassification.ofMap_toMap
assert_compatible GUT.YukawaClassification.scalarMultiple => Physics.YukawaClassification.scalarMultiple
assert_compatible GUT.YukawaClassification.scalarMultiple_apply => Physics.YukawaClassification.scalarMultiple_apply
assert_compatible GUT.YukawaClassification.toMap => Physics.YukawaClassification.toMap
assert_compatible GUT.YukawaClassification.toMap_ofMap => Physics.YukawaClassification.toMap_ofMap
