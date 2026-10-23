import Physics.StandardModel.Operators.Support.Coordinates.SMHiggsStringExtraction
import Physics.StandardModel.Operators.SMSparseCharacter
import Math.RepresentationTheory.WeightStringExtraction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMHiggsStringExtraction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMComputableCharacter.terms.eq_1 => Physics.SMComputableCharacter.terms.eq_1,
  GUT.SMHiggsStringExtraction.a2Extract => Physics.SMHiggsStringExtraction.a2Extract,
  GUT.SMHiggsStringExtraction.a2Extract.eq_1 => Physics.SMHiggsStringExtraction.a2Extract.eq_1,
  GUT.SMHiggsStringExtraction.a2Extract_eq => Physics.SMHiggsStringExtraction.a2Extract_eq,
  GUT.SMHiggsStringExtraction.cached_source => Physics.SMHiggsStringExtraction.cached_source,
  GUT.SMHiggsStringExtraction.coefficient_string => Physics.SMHiggsStringExtraction.coefficient_string,
  GUT.SMHiggsStringExtraction.colorRoots => Physics.SMHiggsStringExtraction.colorRoots,
  GUT.SMHiggsStringExtraction.colorRoots.eq_1 => Physics.SMHiggsStringExtraction.colorRoots.eq_1,
  GUT.SMHiggsStringExtraction.extract => Physics.SMHiggsStringExtraction.extract,
  GUT.SMHiggsStringExtraction.extract.eq_1 => Physics.SMHiggsStringExtraction.extract.eq_1,
  GUT.SMHiggsStringExtraction.keyMatches => Physics.SMHiggsStringExtraction.keyMatches,
  GUT.SMHiggsStringExtraction.keyMatches.eq_1 => Physics.SMHiggsStringExtraction.keyMatches.eq_1,
  GUT.SMHiggsStringExtraction.keyMatches_eq => Physics.SMHiggsStringExtraction.keyMatches_eq,
  GUT.SMHiggsStringExtraction.lookup => Physics.SMHiggsStringExtraction.lookup,
  GUT.SMHiggsStringExtraction.lookup.eq_1 => Physics.SMHiggsStringExtraction.lookup.eq_1,
  GUT.SMHiggsStringExtraction.lookup.eq_2 => Physics.SMHiggsStringExtraction.lookup.eq_2,
  GUT.SMHiggsStringExtraction.lookup.eq_def => Physics.SMHiggsStringExtraction.lookup.eq_def,
  GUT.SMHiggsStringExtraction.lookup_eq => Physics.SMHiggsStringExtraction.lookup_eq,
  GUT.SMHiggsStringExtraction.multiplicity => Physics.SMHiggsStringExtraction.multiplicity,
  GUT.SMHiggsStringExtraction.multiplicity.eq_1 => Physics.SMHiggsStringExtraction.multiplicity.eq_1,
  GUT.SMHiggsStringExtraction.multiplicityWith => Physics.SMHiggsStringExtraction.multiplicityWith,
  GUT.SMHiggsStringExtraction.multiplicityWith.eq_1 => Physics.SMHiggsStringExtraction.multiplicityWith.eq_1,
  GUT.SMHiggsStringExtraction.multiplicity_eq => Physics.SMHiggsStringExtraction.multiplicity_eq,
  GUT.SMHiggsStringExtraction.offset => Physics.SMHiggsStringExtraction.offset,
  GUT.SMHiggsStringExtraction.offset.eq_1 => Physics.SMHiggsStringExtraction.offset.eq_1,
  GUT.SMHiggsStringExtraction.packed_reference => Physics.SMHiggsStringExtraction.packed_reference,
  GUT.SMHiggsStringExtraction.reducedRoots => Physics.SMHiggsStringExtraction.reducedRoots,
  GUT.SMHiggsStringExtraction.reducedRoots.eq_1 => Physics.SMHiggsStringExtraction.reducedRoots.eq_1,
  GUT.SMHiggsStringExtraction.spinRoots => Physics.SMHiggsStringExtraction.spinRoots,
  GUT.SMHiggsStringExtraction.weak => Physics.SMHiggsStringExtraction.weak,
  GUT.SMHiggsStringExtraction.weak.eq_1 => Physics.SMHiggsStringExtraction.weak.eq_1,
  GUT.SMSparseCharacter.multiplicity.eq_1 => Physics.SMSparseCharacter.multiplicity.eq_1,
  GUT.SMSparseCharacter.unpack.eq_1 => Physics.SMSparseCharacter.unpack.eq_1
]

assert_compatible GUT.SMComputableCharacter.terms.eq_1 => Physics.SMComputableCharacter.terms.eq_1
assert_compatible GUT.SMHiggsStringExtraction.a2Extract => Physics.SMHiggsStringExtraction.a2Extract
assert_compatible GUT.SMHiggsStringExtraction.a2Extract.eq_1 => Physics.SMHiggsStringExtraction.a2Extract.eq_1
assert_compatible GUT.SMHiggsStringExtraction.a2Extract_eq => Physics.SMHiggsStringExtraction.a2Extract_eq
assert_compatible GUT.SMHiggsStringExtraction.cached_source => Physics.SMHiggsStringExtraction.cached_source
assert_compatible GUT.SMHiggsStringExtraction.coefficient_string => Physics.SMHiggsStringExtraction.coefficient_string
assert_compatible GUT.SMHiggsStringExtraction.colorRoots => Physics.SMHiggsStringExtraction.colorRoots
assert_compatible GUT.SMHiggsStringExtraction.colorRoots.eq_1 => Physics.SMHiggsStringExtraction.colorRoots.eq_1
assert_compatible GUT.SMHiggsStringExtraction.extract => Physics.SMHiggsStringExtraction.extract
assert_compatible GUT.SMHiggsStringExtraction.extract.eq_1 => Physics.SMHiggsStringExtraction.extract.eq_1
assert_compatible GUT.SMHiggsStringExtraction.keyMatches => Physics.SMHiggsStringExtraction.keyMatches
assert_compatible GUT.SMHiggsStringExtraction.keyMatches.eq_1 => Physics.SMHiggsStringExtraction.keyMatches.eq_1
assert_compatible GUT.SMHiggsStringExtraction.keyMatches_eq => Physics.SMHiggsStringExtraction.keyMatches_eq
assert_compatible GUT.SMHiggsStringExtraction.lookup => Physics.SMHiggsStringExtraction.lookup
assert_compatible GUT.SMHiggsStringExtraction.lookup.eq_1 => Physics.SMHiggsStringExtraction.lookup.eq_1
assert_compatible GUT.SMHiggsStringExtraction.lookup.eq_2 => Physics.SMHiggsStringExtraction.lookup.eq_2
assert_compatible GUT.SMHiggsStringExtraction.lookup.eq_def => Physics.SMHiggsStringExtraction.lookup.eq_def
assert_compatible GUT.SMHiggsStringExtraction.lookup_eq => Physics.SMHiggsStringExtraction.lookup_eq
assert_compatible GUT.SMHiggsStringExtraction.multiplicity => Physics.SMHiggsStringExtraction.multiplicity
assert_compatible GUT.SMHiggsStringExtraction.multiplicity.eq_1 => Physics.SMHiggsStringExtraction.multiplicity.eq_1
assert_compatible GUT.SMHiggsStringExtraction.multiplicityWith => Physics.SMHiggsStringExtraction.multiplicityWith
assert_compatible GUT.SMHiggsStringExtraction.multiplicityWith.eq_1 => Physics.SMHiggsStringExtraction.multiplicityWith.eq_1
assert_compatible GUT.SMHiggsStringExtraction.multiplicity_eq => Physics.SMHiggsStringExtraction.multiplicity_eq
assert_compatible GUT.SMHiggsStringExtraction.offset => Physics.SMHiggsStringExtraction.offset
assert_compatible GUT.SMHiggsStringExtraction.offset.eq_1 => Physics.SMHiggsStringExtraction.offset.eq_1
assert_compatible GUT.SMHiggsStringExtraction.packed_reference => Physics.SMHiggsStringExtraction.packed_reference
assert_compatible GUT.SMHiggsStringExtraction.reducedRoots => Physics.SMHiggsStringExtraction.reducedRoots
assert_compatible GUT.SMHiggsStringExtraction.reducedRoots.eq_1 => Physics.SMHiggsStringExtraction.reducedRoots.eq_1
assert_compatible GUT.SMHiggsStringExtraction.spinRoots => Physics.SMHiggsStringExtraction.spinRoots
assert_compatible GUT.SMHiggsStringExtraction.weak => Physics.SMHiggsStringExtraction.weak
assert_compatible GUT.SMHiggsStringExtraction.weak.eq_1 => Physics.SMHiggsStringExtraction.weak.eq_1
assert_compatible GUT.SMSparseCharacter.multiplicity.eq_1 => Physics.SMSparseCharacter.multiplicity.eq_1
assert_compatible GUT.SMSparseCharacter.unpack.eq_1 => Physics.SMSparseCharacter.unpack.eq_1
