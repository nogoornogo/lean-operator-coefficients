import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHermitian
import Physics.StandardModel.Operators.DevMohapatraExternalLeg
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraHermitian instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.DevMohapatraHermitian.action => Physics.DevMohapatraHermitian.action,
  GUT.DevMohapatraHermitian.action.eq_1 => Physics.DevMohapatraHermitian.action.eq_1,
  GUT.DevMohapatraHermitian.action_effective_hermitian => Physics.DevMohapatraHermitian.action_effective_hermitian,
  GUT.DevMohapatraHermitian.action_hermitian => Physics.DevMohapatraHermitian.action_hermitian,
  GUT.DevMohapatraHermitian.action_scalar_on_shell => Physics.DevMohapatraHermitian.action_scalar_on_shell,
  GUT.DevMohapatraHermitian.complexifiedScalar => Physics.DevMohapatraHermitian.complexifiedScalar,
  GUT.DevMohapatraHermitian.complexifiedScalar.eq_1 => Physics.DevMohapatraHermitian.complexifiedScalar.eq_1,
  GUT.DevMohapatraHermitian.effectiveAction => Physics.DevMohapatraHermitian.effectiveAction,
  GUT.DevMohapatraHermitian.effectiveAction.eq_1 => Physics.DevMohapatraHermitian.effectiveAction.eq_1,
  GUT.DevMohapatraHermitian.effective_expansion => Physics.DevMohapatraHermitian.effective_expansion,
  GUT.DevMohapatraHermitian.effective_hermitian => Physics.DevMohapatraHermitian.effective_hermitian,
  GUT.DevMohapatraHermitian.effective_projection => Physics.DevMohapatraHermitian.effective_projection,
  GUT.DevMohapatraHermitian.hermitian_on_shell => Physics.DevMohapatraHermitian.hermitian_on_shell,
  GUT.DevMohapatraHermitian.leftSource => Physics.DevMohapatraHermitian.leftSource,
  GUT.DevMohapatraHermitian.leftSource.eq_1 => Physics.DevMohapatraHermitian.leftSource.eq_1,
  GUT.DevMohapatraHermitian.massAction => Physics.DevMohapatraHermitian.massAction,
  GUT.DevMohapatraHermitian.massAction.eq_1 => Physics.DevMohapatraHermitian.massAction.eq_1,
  GUT.DevMohapatraHermitian.mass_dictionary => Physics.DevMohapatraHermitian.mass_dictionary,
  GUT.DevMohapatraHermitian.mass_hermitian => Physics.DevMohapatraHermitian.mass_hermitian,
  GUT.DevMohapatraHermitian.rightSource => Physics.DevMohapatraHermitian.rightSource,
  GUT.DevMohapatraHermitian.rightSource.eq_1 => Physics.DevMohapatraHermitian.rightSource.eq_1,
  GUT.DevMohapatraHermitian.scalarAction => Physics.DevMohapatraHermitian.scalarAction,
  GUT.DevMohapatraHermitian.scalarAction.eq_1 => Physics.DevMohapatraHermitian.scalarAction.eq_1,
  GUT.DevMohapatraHermitian.scalarEffective => Physics.DevMohapatraHermitian.scalarEffective,
  GUT.DevMohapatraHermitian.scalarEffective.eq_1 => Physics.DevMohapatraHermitian.scalarEffective.eq_1,
  GUT.DevMohapatraHermitian.scalar_dictionary => Physics.DevMohapatraHermitian.scalar_dictionary,
  GUT.DevMohapatraHermitian.scalar_hermitian => Physics.DevMohapatraHermitian.scalar_hermitian,
  GUT.DevMohapatraHermitian.scalar_on_shell => Physics.DevMohapatraHermitian.scalar_on_shell,
  GUT.DevMohapatraHermitian.solutions_conjugate => Physics.DevMohapatraHermitian.solutions_conjugate,
  GUT.DevMohapatraHermitian.sources_conjugate => Physics.DevMohapatraHermitian.sources_conjugate,
  GUT.DevMohapatraHermitian.vertex => Physics.DevMohapatraHermitian.vertex,
  GUT.DevMohapatraHermitian.vertex.eq_1 => Physics.DevMohapatraHermitian.vertex.eq_1
]

assert_compatible GUT.DevMohapatraHermitian.action => Physics.DevMohapatraHermitian.action
assert_compatible GUT.DevMohapatraHermitian.action.eq_1 => Physics.DevMohapatraHermitian.action.eq_1
assert_compatible GUT.DevMohapatraHermitian.action_effective_hermitian => Physics.DevMohapatraHermitian.action_effective_hermitian
assert_compatible GUT.DevMohapatraHermitian.action_hermitian => Physics.DevMohapatraHermitian.action_hermitian
assert_compatible GUT.DevMohapatraHermitian.action_scalar_on_shell => Physics.DevMohapatraHermitian.action_scalar_on_shell
assert_compatible GUT.DevMohapatraHermitian.complexifiedScalar => Physics.DevMohapatraHermitian.complexifiedScalar
assert_compatible GUT.DevMohapatraHermitian.complexifiedScalar.eq_1 => Physics.DevMohapatraHermitian.complexifiedScalar.eq_1
assert_compatible GUT.DevMohapatraHermitian.effectiveAction => Physics.DevMohapatraHermitian.effectiveAction
assert_compatible GUT.DevMohapatraHermitian.effectiveAction.eq_1 => Physics.DevMohapatraHermitian.effectiveAction.eq_1
assert_compatible GUT.DevMohapatraHermitian.effective_expansion => Physics.DevMohapatraHermitian.effective_expansion
assert_compatible GUT.DevMohapatraHermitian.effective_hermitian => Physics.DevMohapatraHermitian.effective_hermitian
assert_compatible GUT.DevMohapatraHermitian.effective_projection => Physics.DevMohapatraHermitian.effective_projection
assert_compatible GUT.DevMohapatraHermitian.hermitian_on_shell => Physics.DevMohapatraHermitian.hermitian_on_shell
assert_compatible GUT.DevMohapatraHermitian.leftSource => Physics.DevMohapatraHermitian.leftSource
assert_compatible GUT.DevMohapatraHermitian.leftSource.eq_1 => Physics.DevMohapatraHermitian.leftSource.eq_1
assert_compatible GUT.DevMohapatraHermitian.massAction => Physics.DevMohapatraHermitian.massAction
assert_compatible GUT.DevMohapatraHermitian.massAction.eq_1 => Physics.DevMohapatraHermitian.massAction.eq_1
assert_compatible GUT.DevMohapatraHermitian.mass_dictionary => Physics.DevMohapatraHermitian.mass_dictionary
assert_compatible GUT.DevMohapatraHermitian.mass_hermitian => Physics.DevMohapatraHermitian.mass_hermitian
assert_compatible GUT.DevMohapatraHermitian.rightSource => Physics.DevMohapatraHermitian.rightSource
assert_compatible GUT.DevMohapatraHermitian.rightSource.eq_1 => Physics.DevMohapatraHermitian.rightSource.eq_1
assert_compatible GUT.DevMohapatraHermitian.scalarAction => Physics.DevMohapatraHermitian.scalarAction
assert_compatible GUT.DevMohapatraHermitian.scalarAction.eq_1 => Physics.DevMohapatraHermitian.scalarAction.eq_1
assert_compatible GUT.DevMohapatraHermitian.scalarEffective => Physics.DevMohapatraHermitian.scalarEffective
assert_compatible GUT.DevMohapatraHermitian.scalarEffective.eq_1 => Physics.DevMohapatraHermitian.scalarEffective.eq_1
assert_compatible GUT.DevMohapatraHermitian.scalar_dictionary => Physics.DevMohapatraHermitian.scalar_dictionary
assert_compatible GUT.DevMohapatraHermitian.scalar_hermitian => Physics.DevMohapatraHermitian.scalar_hermitian
assert_compatible GUT.DevMohapatraHermitian.scalar_on_shell => Physics.DevMohapatraHermitian.scalar_on_shell
assert_compatible GUT.DevMohapatraHermitian.solutions_conjugate => Physics.DevMohapatraHermitian.solutions_conjugate
assert_compatible GUT.DevMohapatraHermitian.sources_conjugate => Physics.DevMohapatraHermitian.sources_conjugate
assert_compatible GUT.DevMohapatraHermitian.vertex => Physics.DevMohapatraHermitian.vertex
assert_compatible GUT.DevMohapatraHermitian.vertex.eq_1 => Physics.DevMohapatraHermitian.vertex.eq_1
