import Physics.FieldTheory.Mass.Flavor.FlavorMajoranaLine
import Physics.FieldTheory.Yukawa.FlavorStabilizer
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Flavor.FlavorMajoranaLine instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FlavorMajoranaLine.accidental_strict => Physics.FlavorMajoranaLine.accidental_strict,
  GUT.FlavorMajoranaLine.coupling => Physics.FlavorMajoranaLine.coupling,
  GUT.FlavorMajoranaLine.coupling.eq_1 => Physics.FlavorMajoranaLine.coupling.eq_1,
  GUT.FlavorMajoranaLine.coupling_evaluation => Physics.FlavorMajoranaLine.coupling_evaluation,
  GUT.FlavorMajoranaLine.coupling_subgroup => Physics.FlavorMajoranaLine.coupling_subgroup,
  GUT.FlavorMajoranaLine.cyclicEquiv => Physics.FlavorMajoranaLine.cyclicEquiv,
  GUT.FlavorMajoranaLine.cyclicRootsEquiv => Physics.FlavorMajoranaLine.cyclicRootsEquiv,
  GUT.FlavorMajoranaLine.evaluated_subgroup => Physics.FlavorMajoranaLine.evaluated_subgroup,
  GUT.FlavorMajoranaLine.form => Physics.FlavorMajoranaLine.form,
  GUT.FlavorMajoranaLine.form.eq_1 => Physics.FlavorMajoranaLine.form.eq_1,
  GUT.FlavorMajoranaLine.form_symmetric => Physics.FlavorMajoranaLine.form_symmetric,
  GUT.FlavorMajoranaLine.mem_iff => Physics.FlavorMajoranaLine.mem_iff,
  GUT.FlavorMajoranaLine.nonzero_card => Physics.FlavorMajoranaLine.nonzero_card,
  GUT.FlavorMajoranaLine.nonzero_subgroup => Physics.FlavorMajoranaLine.nonzero_subgroup,
  GUT.FlavorMajoranaLine.nonzero_vacuum => Physics.FlavorMajoranaLine.nonzero_vacuum,
  GUT.FlavorMajoranaLine.phaseAction => Physics.FlavorMajoranaLine.phaseAction,
  GUT.FlavorMajoranaLine.phaseAction.eq_1 => Physics.FlavorMajoranaLine.phaseAction.eq_1,
  GUT.FlavorMajoranaLine.rootsHom => Physics.FlavorMajoranaLine.rootsHom,
  GUT.FlavorMajoranaLine.rootsHom_bijective => Physics.FlavorMajoranaLine.rootsHom_bijective,
  GUT.FlavorMajoranaLine.subgroup => Physics.FlavorMajoranaLine.subgroup,
  GUT.FlavorMajoranaLine.subgroup.eq_1 => Physics.FlavorMajoranaLine.subgroup.eq_1,
  GUT.FlavorMajoranaLine.zero_subgroup => Physics.FlavorMajoranaLine.zero_subgroup,
  GUT.FlavorMajoranaLine.zero_vacuum => Physics.FlavorMajoranaLine.zero_vacuum
]

assert_compatible GUT.FlavorMajoranaLine.accidental_strict => Physics.FlavorMajoranaLine.accidental_strict
assert_compatible GUT.FlavorMajoranaLine.coupling => Physics.FlavorMajoranaLine.coupling
assert_compatible GUT.FlavorMajoranaLine.coupling.eq_1 => Physics.FlavorMajoranaLine.coupling.eq_1
assert_compatible GUT.FlavorMajoranaLine.coupling_evaluation => Physics.FlavorMajoranaLine.coupling_evaluation
assert_compatible GUT.FlavorMajoranaLine.coupling_subgroup => Physics.FlavorMajoranaLine.coupling_subgroup
assert_compatible GUT.FlavorMajoranaLine.cyclicEquiv => Physics.FlavorMajoranaLine.cyclicEquiv
assert_compatible GUT.FlavorMajoranaLine.cyclicRootsEquiv => Physics.FlavorMajoranaLine.cyclicRootsEquiv
assert_compatible GUT.FlavorMajoranaLine.evaluated_subgroup => Physics.FlavorMajoranaLine.evaluated_subgroup
assert_compatible GUT.FlavorMajoranaLine.form => Physics.FlavorMajoranaLine.form
assert_compatible GUT.FlavorMajoranaLine.form.eq_1 => Physics.FlavorMajoranaLine.form.eq_1
assert_compatible GUT.FlavorMajoranaLine.form_symmetric => Physics.FlavorMajoranaLine.form_symmetric
assert_compatible GUT.FlavorMajoranaLine.mem_iff => Physics.FlavorMajoranaLine.mem_iff
assert_compatible GUT.FlavorMajoranaLine.nonzero_card => Physics.FlavorMajoranaLine.nonzero_card
assert_compatible GUT.FlavorMajoranaLine.nonzero_subgroup => Physics.FlavorMajoranaLine.nonzero_subgroup
assert_compatible GUT.FlavorMajoranaLine.nonzero_vacuum => Physics.FlavorMajoranaLine.nonzero_vacuum
assert_compatible GUT.FlavorMajoranaLine.phaseAction => Physics.FlavorMajoranaLine.phaseAction
assert_compatible GUT.FlavorMajoranaLine.phaseAction.eq_1 => Physics.FlavorMajoranaLine.phaseAction.eq_1
assert_compatible GUT.FlavorMajoranaLine.rootsHom => Physics.FlavorMajoranaLine.rootsHom
assert_compatible GUT.FlavorMajoranaLine.rootsHom_bijective => Physics.FlavorMajoranaLine.rootsHom_bijective
assert_compatible GUT.FlavorMajoranaLine.subgroup => Physics.FlavorMajoranaLine.subgroup
assert_compatible GUT.FlavorMajoranaLine.subgroup.eq_1 => Physics.FlavorMajoranaLine.subgroup.eq_1
assert_compatible GUT.FlavorMajoranaLine.zero_subgroup => Physics.FlavorMajoranaLine.zero_subgroup
assert_compatible GUT.FlavorMajoranaLine.zero_vacuum => Physics.FlavorMajoranaLine.zero_vacuum
