import Physics.StandardModel.Operators.BaryonOne.Qque.LiQqueCoordinates
import Physics.StandardModel.Operators.LiQqueConvention
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.LiQqueCoordinates instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.LiQqueCoordinates.Coordinates => Physics.LiQqueCoordinates.Coordinates,
  GUT.LiQqueCoordinates.flavorBasis => Physics.LiQqueCoordinates.flavorBasis,
  GUT.LiQqueCoordinates.flavorBasis_independent => Physics.LiQqueCoordinates.flavorBasis_independent,
  GUT.LiQqueCoordinates.flavorBasis_is_candidate => Physics.LiQqueCoordinates.flavorBasis_is_candidate,
  GUT.LiQqueCoordinates.flavorBasis_spans => Physics.LiQqueCoordinates.flavorBasis_spans,
  GUT.LiQqueCoordinates.flavorEquiv => Physics.LiQqueCoordinates.flavorEquiv,
  GUT.LiQqueCoordinates.flavor_entry => Physics.LiQqueCoordinates.flavor_entry,
  GUT.LiQqueCoordinates.flavor_index_card => Physics.LiQqueCoordinates.flavor_index_card,
  GUT.LiQqueCoordinates.flavor_inverse_left => Physics.LiQqueCoordinates.flavor_inverse_left,
  GUT.LiQqueCoordinates.flavor_inverse_right => Physics.LiQqueCoordinates.flavor_inverse_right,
  GUT.LiQqueCoordinates.flavor_paperOrdered_apply => Physics.LiQqueCoordinates.flavor_paperOrdered_apply,
  GUT.LiQqueCoordinates.homEquiv => Physics.LiQqueCoordinates.homEquiv,
  GUT.LiQqueCoordinates.homEquiv_entry => Physics.LiQqueCoordinates.homEquiv_entry,
  GUT.LiQqueCoordinates.inverse_is_candidate => Physics.LiQqueCoordinates.inverse_is_candidate,
  GUT.LiQqueCoordinates.inverse_left => Physics.LiQqueCoordinates.inverse_left,
  GUT.LiQqueCoordinates.inverse_right => Physics.LiQqueCoordinates.inverse_right,
  GUT.LiQqueCoordinates.matrixEquiv => Physics.LiQqueCoordinates.matrixEquiv,
  GUT.LiQqueCoordinates.matrixEquiv.eq_1 => Physics.LiQqueCoordinates.matrixEquiv.eq_1,
  GUT.LiQqueCoordinates.matrixSpace => Physics.LiQqueCoordinates.matrixSpace,
  GUT.LiQqueCoordinates.mem_matrixSpace_iff => Physics.LiQqueCoordinates.mem_matrixSpace_iff,
  GUT.LiQqueCoordinates.residual_entry => Physics.LiQqueCoordinates.residual_entry,
  GUT.LiQqueCoordinates.sectorEquiv => Physics.LiQqueCoordinates.sectorEquiv,
  GUT.LiQqueCoordinates.sectorEquiv_symm_apply => Physics.LiQqueCoordinates.sectorEquiv_symm_apply,
  GUT.LiQqueCoordinates.trivialHomEquiv => Physics.LiQqueCoordinates.trivialHomEquiv
]

assert_compatible GUT.LiQqueCoordinates.Coordinates => Physics.LiQqueCoordinates.Coordinates
assert_compatible GUT.LiQqueCoordinates.flavorBasis => Physics.LiQqueCoordinates.flavorBasis
assert_compatible GUT.LiQqueCoordinates.flavorBasis_independent => Physics.LiQqueCoordinates.flavorBasis_independent
assert_compatible GUT.LiQqueCoordinates.flavorBasis_is_candidate => Physics.LiQqueCoordinates.flavorBasis_is_candidate
assert_compatible GUT.LiQqueCoordinates.flavorBasis_spans => Physics.LiQqueCoordinates.flavorBasis_spans
assert_compatible GUT.LiQqueCoordinates.flavorEquiv => Physics.LiQqueCoordinates.flavorEquiv
assert_compatible GUT.LiQqueCoordinates.flavor_entry => Physics.LiQqueCoordinates.flavor_entry
assert_compatible GUT.LiQqueCoordinates.flavor_index_card => Physics.LiQqueCoordinates.flavor_index_card
assert_compatible GUT.LiQqueCoordinates.flavor_inverse_left => Physics.LiQqueCoordinates.flavor_inverse_left
assert_compatible GUT.LiQqueCoordinates.flavor_inverse_right => Physics.LiQqueCoordinates.flavor_inverse_right
assert_compatible GUT.LiQqueCoordinates.flavor_paperOrdered_apply => Physics.LiQqueCoordinates.flavor_paperOrdered_apply
assert_compatible GUT.LiQqueCoordinates.homEquiv => Physics.LiQqueCoordinates.homEquiv
assert_compatible GUT.LiQqueCoordinates.homEquiv_entry => Physics.LiQqueCoordinates.homEquiv_entry
assert_compatible GUT.LiQqueCoordinates.inverse_is_candidate => Physics.LiQqueCoordinates.inverse_is_candidate
assert_compatible GUT.LiQqueCoordinates.inverse_left => Physics.LiQqueCoordinates.inverse_left
assert_compatible GUT.LiQqueCoordinates.inverse_right => Physics.LiQqueCoordinates.inverse_right
assert_compatible GUT.LiQqueCoordinates.matrixEquiv => Physics.LiQqueCoordinates.matrixEquiv
assert_compatible GUT.LiQqueCoordinates.matrixEquiv.eq_1 => Physics.LiQqueCoordinates.matrixEquiv.eq_1
assert_compatible GUT.LiQqueCoordinates.matrixSpace => Physics.LiQqueCoordinates.matrixSpace
assert_compatible GUT.LiQqueCoordinates.mem_matrixSpace_iff => Physics.LiQqueCoordinates.mem_matrixSpace_iff
assert_compatible GUT.LiQqueCoordinates.residual_entry => Physics.LiQqueCoordinates.residual_entry
assert_compatible GUT.LiQqueCoordinates.sectorEquiv => Physics.LiQqueCoordinates.sectorEquiv
assert_compatible GUT.LiQqueCoordinates.sectorEquiv_symm_apply => Physics.LiQqueCoordinates.sectorEquiv_symm_apply
assert_compatible GUT.LiQqueCoordinates.trivialHomEquiv => Physics.LiQqueCoordinates.trivialHomEquiv
