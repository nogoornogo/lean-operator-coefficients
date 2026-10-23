import Physics.StandardModel.Operators.BaryonOne.Qque.FullLightSpeciesQque
import Physics.StandardModel.Operators.QqueCoefficientCompleteness
import Physics.StandardModel.Gauge.LightSMFieldExtraction
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.FullLightSpeciesQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FullLightSpeciesQque.E => Physics.FullLightSpeciesQque.E,
  GUT.FullLightSpeciesQque.HasCoefficient => Physics.FullLightSpeciesQque.HasCoefficient,
  GUT.FullLightSpeciesQque.HasResidualMap => Physics.FullLightSpeciesQque.HasResidualMap,
  GUT.FullLightSpeciesQque.Q => Physics.FullLightSpeciesQque.Q,
  GUT.FullLightSpeciesQque.ResidualHom => Physics.FullLightSpeciesQque.ResidualHom,
  GUT.FullLightSpeciesQque.Sector => Physics.FullLightSpeciesQque.Sector,
  GUT.FullLightSpeciesQque.U => Physics.FullLightSpeciesQque.U,
  GUT.FullLightSpeciesQque.all_forbidden_iff => Physics.FullLightSpeciesQque.all_forbidden_iff,
  GUT.FullLightSpeciesQque.electronEquiv => Physics.FullLightSpeciesQque.electronEquiv,
  GUT.FullLightSpeciesQque.electron_mem => Physics.FullLightSpeciesQque.electron_mem,
  GUT.FullLightSpeciesQque.equiv => Physics.FullLightSpeciesQque.equiv,
  GUT.FullLightSpeciesQque.fields => Physics.FullLightSpeciesQque.fields,
  GUT.FullLightSpeciesQque.nonzero_iff => Physics.FullLightSpeciesQque.nonzero_iff,
  GUT.FullLightSpeciesQque.quarkEquiv => Physics.FullLightSpeciesQque.quarkEquiv,
  GUT.FullLightSpeciesQque.quark_mem => Physics.FullLightSpeciesQque.quark_mem,
  GUT.FullLightSpeciesQque.rightMultiplicityEquiv => Physics.FullLightSpeciesQque.rightMultiplicityEquiv,
  GUT.FullLightSpeciesQque.suppliedFieldsEquiv => Physics.FullLightSpeciesQque.suppliedFieldsEquiv,
  GUT.FullLightSpeciesQque.supplied_alternation_iff => Physics.FullLightSpeciesQque.supplied_alternation_iff,
  GUT.FullLightSpeciesQque.upEquiv => Physics.FullLightSpeciesQque.upEquiv,
  GUT.FullLightSpeciesQque.up_mem => Physics.FullLightSpeciesQque.up_mem
]

assert_compatible GUT.FullLightSpeciesQque.E => Physics.FullLightSpeciesQque.E
assert_compatible GUT.FullLightSpeciesQque.HasCoefficient => Physics.FullLightSpeciesQque.HasCoefficient
assert_compatible GUT.FullLightSpeciesQque.HasResidualMap => Physics.FullLightSpeciesQque.HasResidualMap
assert_compatible GUT.FullLightSpeciesQque.Q => Physics.FullLightSpeciesQque.Q
assert_compatible GUT.FullLightSpeciesQque.ResidualHom => Physics.FullLightSpeciesQque.ResidualHom
assert_compatible GUT.FullLightSpeciesQque.Sector => Physics.FullLightSpeciesQque.Sector
assert_compatible GUT.FullLightSpeciesQque.U => Physics.FullLightSpeciesQque.U
assert_compatible GUT.FullLightSpeciesQque.all_forbidden_iff => Physics.FullLightSpeciesQque.all_forbidden_iff
assert_compatible GUT.FullLightSpeciesQque.electronEquiv => Physics.FullLightSpeciesQque.electronEquiv
assert_compatible GUT.FullLightSpeciesQque.electron_mem => Physics.FullLightSpeciesQque.electron_mem
assert_compatible GUT.FullLightSpeciesQque.equiv => Physics.FullLightSpeciesQque.equiv
assert_compatible GUT.FullLightSpeciesQque.fields => Physics.FullLightSpeciesQque.fields
assert_compatible GUT.FullLightSpeciesQque.nonzero_iff => Physics.FullLightSpeciesQque.nonzero_iff
assert_compatible GUT.FullLightSpeciesQque.quarkEquiv => Physics.FullLightSpeciesQque.quarkEquiv
assert_compatible GUT.FullLightSpeciesQque.quark_mem => Physics.FullLightSpeciesQque.quark_mem
assert_compatible GUT.FullLightSpeciesQque.rightMultiplicityEquiv => Physics.FullLightSpeciesQque.rightMultiplicityEquiv
assert_compatible GUT.FullLightSpeciesQque.suppliedFieldsEquiv => Physics.FullLightSpeciesQque.suppliedFieldsEquiv
assert_compatible GUT.FullLightSpeciesQque.supplied_alternation_iff => Physics.FullLightSpeciesQque.supplied_alternation_iff
assert_compatible GUT.FullLightSpeciesQque.upEquiv => Physics.FullLightSpeciesQque.upEquiv
assert_compatible GUT.FullLightSpeciesQque.up_mem => Physics.FullLightSpeciesQque.up_mem
