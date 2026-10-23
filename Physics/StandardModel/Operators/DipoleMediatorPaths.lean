import Physics.StandardModel.Operators.Dipole.DipoleMediatorPaths
import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.LinearAlgebra.WeightedSelectedPaths
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.DipoleMediatorPaths instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DipoleFlavorSelection.selector.congr_simp => Physics.DipoleFlavorSelection.selector.congr_simp,
  GUT.DipoleMediatorPaths.exists_nonzero_iff_path => Physics.DipoleMediatorPaths.exists_nonzero_iff_path,
  GUT.DipoleMediatorPaths.generation => Physics.DipoleMediatorPaths.generation,
  GUT.DipoleMediatorPaths.generation.congr_simp => Physics.DipoleMediatorPaths.generation.congr_simp,
  GUT.DipoleMediatorPaths.generation.eq_1 => Physics.DipoleMediatorPaths.generation.eq_1,
  GUT.DipoleMediatorPaths.nonzero_iff => Physics.DipoleMediatorPaths.nonzero_iff,
  GUT.DipoleMediatorPaths.nonzero_of_mediator_witness => Physics.DipoleMediatorPaths.nonzero_of_mediator_witness,
  GUT.DipoleMediatorPaths.nonzero_of_single_selected_path => Physics.DipoleMediatorPaths.nonzero_of_single_selected_path,
  GUT.DipoleMediatorPaths.path_selected => Physics.DipoleMediatorPaths.path_selected,
  GUT.DipoleMediatorPaths.paths => Physics.DipoleMediatorPaths.paths,
  GUT.DipoleMediatorPaths.realized_iff_path_of_factorization => Physics.DipoleMediatorPaths.realized_iff_path_of_factorization,
  GUT.DipoleMediatorPaths.selected => Physics.DipoleMediatorPaths.selected,
  GUT.DipoleMediatorPaths.selected_of_factorization => Physics.DipoleMediatorPaths.selected_of_factorization,
  GUT.DipoleSMCoefficient.equiv.congr_simp => Physics.DipoleSMCoefficient.equiv.congr_simp
]

assert_compatible GUT.DipoleFlavorSelection.selector.congr_simp => Physics.DipoleFlavorSelection.selector.congr_simp
assert_compatible GUT.DipoleMediatorPaths.exists_nonzero_iff_path => Physics.DipoleMediatorPaths.exists_nonzero_iff_path
assert_compatible GUT.DipoleMediatorPaths.generation => Physics.DipoleMediatorPaths.generation
assert_compatible GUT.DipoleMediatorPaths.generation.congr_simp => Physics.DipoleMediatorPaths.generation.congr_simp
assert_compatible GUT.DipoleMediatorPaths.generation.eq_1 => Physics.DipoleMediatorPaths.generation.eq_1
assert_compatible GUT.DipoleMediatorPaths.nonzero_iff => Physics.DipoleMediatorPaths.nonzero_iff
assert_compatible GUT.DipoleMediatorPaths.nonzero_of_mediator_witness => Physics.DipoleMediatorPaths.nonzero_of_mediator_witness
assert_compatible GUT.DipoleMediatorPaths.nonzero_of_single_selected_path => Physics.DipoleMediatorPaths.nonzero_of_single_selected_path
assert_compatible GUT.DipoleMediatorPaths.path_selected => Physics.DipoleMediatorPaths.path_selected
assert_compatible GUT.DipoleMediatorPaths.paths => Physics.DipoleMediatorPaths.paths
assert_compatible GUT.DipoleMediatorPaths.realized_iff_path_of_factorization => Physics.DipoleMediatorPaths.realized_iff_path_of_factorization
assert_compatible GUT.DipoleMediatorPaths.selected => Physics.DipoleMediatorPaths.selected
assert_compatible GUT.DipoleMediatorPaths.selected_of_factorization => Physics.DipoleMediatorPaths.selected_of_factorization
assert_compatible GUT.DipoleSMCoefficient.equiv.congr_simp => Physics.DipoleSMCoefficient.equiv.congr_simp
