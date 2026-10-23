import Physics.StandardModel.Operators.Dipole.S3DipoleSelection
import Physics.StandardModel.Operators.DipoleFlavorSelection
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Dipole.S3DipoleSelection instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.S3DipoleSelection.H => Physics.S3DipoleSelection.H,
  GUT.S3DipoleSelection.V => Physics.S3DipoleSelection.V,
  GUT.S3DipoleSelection.action => Physics.S3DipoleSelection.action,
  GUT.S3DipoleSelection.action_apply => Physics.S3DipoleSelection.action_apply,
  GUT.S3DipoleSelection.action_single => Physics.S3DipoleSelection.action_single,
  GUT.S3DipoleSelection.centralizer => Physics.S3DipoleSelection.centralizer,
  GUT.S3DipoleSelection.entries => Physics.S3DipoleSelection.entries,
  GUT.S3DipoleSelection.entry_equivariant => Physics.S3DipoleSelection.entry_equivariant,
  GUT.S3DipoleSelection.generator_relations => Physics.S3DipoleSelection.generator_relations,
  GUT.S3DipoleSelection.noncommuting => Physics.S3DipoleSelection.noncommuting,
  GUT.S3DipoleSelection.normal_forms => Physics.S3DipoleSelection.normal_forms,
  GUT.S3DipoleSelection.off_diagonal_allowed => Physics.S3DipoleSelection.off_diagonal_allowed,
  GUT.S3DipoleSelection.ones => Physics.S3DipoleSelection.ones,
  GUT.S3DipoleSelection.ones.eq_1 => Physics.S3DipoleSelection.ones.eq_1,
  GUT.S3DipoleSelection.selected_allowed_iff => Physics.S3DipoleSelection.selected_allowed_iff,
  GUT.S3DipoleSelection.selected_forbidden_iff => Physics.S3DipoleSelection.selected_forbidden_iff,
  GUT.S3DipoleSelection.sumMap => Physics.S3DipoleSelection.sumMap,
  GUT.S3DipoleSelection.sumMap.eq_1 => Physics.S3DipoleSelection.sumMap.eq_1
]

assert_compatible GUT.S3DipoleSelection.H => Physics.S3DipoleSelection.H
assert_compatible GUT.S3DipoleSelection.V => Physics.S3DipoleSelection.V
assert_compatible GUT.S3DipoleSelection.action => Physics.S3DipoleSelection.action
assert_compatible GUT.S3DipoleSelection.action_apply => Physics.S3DipoleSelection.action_apply
assert_compatible GUT.S3DipoleSelection.action_single => Physics.S3DipoleSelection.action_single
assert_compatible GUT.S3DipoleSelection.centralizer => Physics.S3DipoleSelection.centralizer
assert_compatible GUT.S3DipoleSelection.entries => Physics.S3DipoleSelection.entries
assert_compatible GUT.S3DipoleSelection.entry_equivariant => Physics.S3DipoleSelection.entry_equivariant
assert_compatible GUT.S3DipoleSelection.generator_relations => Physics.S3DipoleSelection.generator_relations
assert_compatible GUT.S3DipoleSelection.noncommuting => Physics.S3DipoleSelection.noncommuting
assert_compatible GUT.S3DipoleSelection.normal_forms => Physics.S3DipoleSelection.normal_forms
assert_compatible GUT.S3DipoleSelection.off_diagonal_allowed => Physics.S3DipoleSelection.off_diagonal_allowed
assert_compatible GUT.S3DipoleSelection.ones => Physics.S3DipoleSelection.ones
assert_compatible GUT.S3DipoleSelection.ones.eq_1 => Physics.S3DipoleSelection.ones.eq_1
assert_compatible GUT.S3DipoleSelection.selected_allowed_iff => Physics.S3DipoleSelection.selected_allowed_iff
assert_compatible GUT.S3DipoleSelection.selected_forbidden_iff => Physics.S3DipoleSelection.selected_forbidden_iff
assert_compatible GUT.S3DipoleSelection.sumMap => Physics.S3DipoleSelection.sumMap
assert_compatible GUT.S3DipoleSelection.sumMap.eq_1 => Physics.S3DipoleSelection.sumMap.eq_1
