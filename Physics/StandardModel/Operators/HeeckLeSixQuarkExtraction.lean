import Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkExtraction
import Physics.StandardModel.Operators.HeeckLeSixQuarkCouplingConnection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.HeeckLe.HeeckLeSixQuarkExtraction instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HeeckLeSixQuarkExtraction.cleaned => Physics.HeeckLeSixQuarkExtraction.cleaned,
  GUT.HeeckLeSixQuarkExtraction.cleaned_apply => Physics.HeeckLeSixQuarkExtraction.cleaned_apply,
  GUT.HeeckLeSixQuarkExtraction.cleaned_assemble => Physics.HeeckLeSixQuarkExtraction.cleaned_assemble,
  GUT.HeeckLeSixQuarkExtraction.coupling => Physics.HeeckLeSixQuarkExtraction.coupling,
  GUT.HeeckLeSixQuarkExtraction.coupling_apply => Physics.HeeckLeSixQuarkExtraction.coupling_apply,
  GUT.HeeckLeSixQuarkExtraction.coupling_assemble => Physics.HeeckLeSixQuarkExtraction.coupling_assemble,
  GUT.HeeckLeSixQuarkExtraction.decode => Physics.HeeckLeSixQuarkExtraction.decode,
  GUT.HeeckLeSixQuarkExtraction.decode_apply => Physics.HeeckLeSixQuarkExtraction.decode_apply,
  GUT.HeeckLeSixQuarkExtraction.decode_assemble => Physics.HeeckLeSixQuarkExtraction.decode_assemble,
  GUT.HeeckLeSixQuarkExtraction.evenCoordinates => Physics.HeeckLeSixQuarkExtraction.evenCoordinates,
  GUT.HeeckLeSixQuarkExtraction.evenCoordinates_apply => Physics.HeeckLeSixQuarkExtraction.evenCoordinates_apply,
  GUT.HeeckLeSixQuarkExtraction.evenCoordinates_assemble => Physics.HeeckLeSixQuarkExtraction.evenCoordinates_assemble,
  GUT.HeeckLeSixQuarkExtraction.extraction => Physics.HeeckLeSixQuarkExtraction.extraction,
  GUT.HeeckLeSixQuarkExtraction.extraction_rawAssembly => Physics.HeeckLeSixQuarkExtraction.extraction_rawAssembly,
  GUT.HeeckLeSixQuarkExtraction.free => Physics.HeeckLeSixQuarkExtraction.free,
  GUT.HeeckLeSixQuarkExtraction.normalized_rawAssembly => Physics.HeeckLeSixQuarkExtraction.normalized_rawAssembly,
  GUT.HeeckLeSixQuarkExtraction.oddCoordinates => Physics.HeeckLeSixQuarkExtraction.oddCoordinates,
  GUT.HeeckLeSixQuarkExtraction.oddCoordinates_apply => Physics.HeeckLeSixQuarkExtraction.oddCoordinates_apply,
  GUT.HeeckLeSixQuarkExtraction.oddCoordinates_assemble => Physics.HeeckLeSixQuarkExtraction.oddCoordinates_assemble,
  GUT.HeeckLeSixQuarkExtraction.rawAssembly => Physics.HeeckLeSixQuarkExtraction.rawAssembly,
  GUT.HeeckLeSixQuarkExtraction.remainder => Physics.HeeckLeSixQuarkExtraction.remainder,
  GUT.HeeckLeSixQuarkExtraction.remainder_apply => Physics.HeeckLeSixQuarkExtraction.remainder_apply,
  GUT.HeeckLeSixQuarkExtraction.remainder_assemble => Physics.HeeckLeSixQuarkExtraction.remainder_assemble,
  GUT.HeeckLeSixQuarkExtraction.source0Coordinates => Physics.HeeckLeSixQuarkExtraction.source0Coordinates,
  GUT.HeeckLeSixQuarkExtraction.source0Coordinates_apply => Physics.HeeckLeSixQuarkExtraction.source0Coordinates_apply,
  GUT.HeeckLeSixQuarkExtraction.source0Coordinates_assemble => Physics.HeeckLeSixQuarkExtraction.source0Coordinates_assemble,
  GUT.HeeckLeSixQuarkExtraction.source1Coordinates => Physics.HeeckLeSixQuarkExtraction.source1Coordinates,
  GUT.HeeckLeSixQuarkExtraction.source1Coordinates_apply => Physics.HeeckLeSixQuarkExtraction.source1Coordinates_apply,
  GUT.HeeckLeSixQuarkExtraction.source1Coordinates_assemble => Physics.HeeckLeSixQuarkExtraction.source1Coordinates_assemble,
  GUT.HeeckLeSixQuarkExtraction.trueCoupling => Physics.HeeckLeSixQuarkExtraction.trueCoupling,
  GUT.HeeckLeSixQuarkExtraction.trueCoupling_3 => Physics.HeeckLeSixQuarkExtraction.trueCoupling_3,
  GUT.HeeckLeSixQuarkExtraction.trueCoupling_4 => Physics.HeeckLeSixQuarkExtraction.trueCoupling_4,
  GUT.HeeckLeSixQuarkExtraction.trueCoupling_left => Physics.HeeckLeSixQuarkExtraction.trueCoupling_left,
  GUT.LiSixQuarkReducedAction.extraction.congr_simp => Physics.LiSixQuarkReducedAction.extraction.congr_simp
]

assert_compatible GUT.HeeckLeSixQuarkExtraction.cleaned => Physics.HeeckLeSixQuarkExtraction.cleaned
assert_compatible GUT.HeeckLeSixQuarkExtraction.cleaned_apply => Physics.HeeckLeSixQuarkExtraction.cleaned_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.cleaned_assemble => Physics.HeeckLeSixQuarkExtraction.cleaned_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.coupling => Physics.HeeckLeSixQuarkExtraction.coupling
assert_compatible GUT.HeeckLeSixQuarkExtraction.coupling_apply => Physics.HeeckLeSixQuarkExtraction.coupling_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.coupling_assemble => Physics.HeeckLeSixQuarkExtraction.coupling_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.decode => Physics.HeeckLeSixQuarkExtraction.decode
assert_compatible GUT.HeeckLeSixQuarkExtraction.decode_apply => Physics.HeeckLeSixQuarkExtraction.decode_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.decode_assemble => Physics.HeeckLeSixQuarkExtraction.decode_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.evenCoordinates => Physics.HeeckLeSixQuarkExtraction.evenCoordinates
assert_compatible GUT.HeeckLeSixQuarkExtraction.evenCoordinates_apply => Physics.HeeckLeSixQuarkExtraction.evenCoordinates_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.evenCoordinates_assemble => Physics.HeeckLeSixQuarkExtraction.evenCoordinates_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.extraction => Physics.HeeckLeSixQuarkExtraction.extraction
assert_compatible GUT.HeeckLeSixQuarkExtraction.extraction_rawAssembly => Physics.HeeckLeSixQuarkExtraction.extraction_rawAssembly
assert_compatible GUT.HeeckLeSixQuarkExtraction.free => Physics.HeeckLeSixQuarkExtraction.free
assert_compatible GUT.HeeckLeSixQuarkExtraction.normalized_rawAssembly => Physics.HeeckLeSixQuarkExtraction.normalized_rawAssembly
assert_compatible GUT.HeeckLeSixQuarkExtraction.oddCoordinates => Physics.HeeckLeSixQuarkExtraction.oddCoordinates
assert_compatible GUT.HeeckLeSixQuarkExtraction.oddCoordinates_apply => Physics.HeeckLeSixQuarkExtraction.oddCoordinates_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.oddCoordinates_assemble => Physics.HeeckLeSixQuarkExtraction.oddCoordinates_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.rawAssembly => Physics.HeeckLeSixQuarkExtraction.rawAssembly
assert_compatible GUT.HeeckLeSixQuarkExtraction.remainder => Physics.HeeckLeSixQuarkExtraction.remainder
assert_compatible GUT.HeeckLeSixQuarkExtraction.remainder_apply => Physics.HeeckLeSixQuarkExtraction.remainder_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.remainder_assemble => Physics.HeeckLeSixQuarkExtraction.remainder_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.source0Coordinates => Physics.HeeckLeSixQuarkExtraction.source0Coordinates
assert_compatible GUT.HeeckLeSixQuarkExtraction.source0Coordinates_apply => Physics.HeeckLeSixQuarkExtraction.source0Coordinates_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.source0Coordinates_assemble => Physics.HeeckLeSixQuarkExtraction.source0Coordinates_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.source1Coordinates => Physics.HeeckLeSixQuarkExtraction.source1Coordinates
assert_compatible GUT.HeeckLeSixQuarkExtraction.source1Coordinates_apply => Physics.HeeckLeSixQuarkExtraction.source1Coordinates_apply
assert_compatible GUT.HeeckLeSixQuarkExtraction.source1Coordinates_assemble => Physics.HeeckLeSixQuarkExtraction.source1Coordinates_assemble
assert_compatible GUT.HeeckLeSixQuarkExtraction.trueCoupling => Physics.HeeckLeSixQuarkExtraction.trueCoupling
assert_compatible GUT.HeeckLeSixQuarkExtraction.trueCoupling_3 => Physics.HeeckLeSixQuarkExtraction.trueCoupling_3
assert_compatible GUT.HeeckLeSixQuarkExtraction.trueCoupling_4 => Physics.HeeckLeSixQuarkExtraction.trueCoupling_4
assert_compatible GUT.HeeckLeSixQuarkExtraction.trueCoupling_left => Physics.HeeckLeSixQuarkExtraction.trueCoupling_left
assert_compatible GUT.LiSixQuarkReducedAction.extraction.congr_simp => Physics.LiSixQuarkReducedAction.extraction.congr_simp
