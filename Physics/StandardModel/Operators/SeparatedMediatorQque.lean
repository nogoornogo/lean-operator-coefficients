import Physics.StandardModel.Operators.BaryonOne.Qque.SeparatedMediatorQque
import Physics.StandardModel.Operators.QqueMediatorInheritance
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qque.SeparatedMediatorQque instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SeparatedMediatorQque.coreSector => Physics.SeparatedMediatorQque.coreSector,
  GUT.SeparatedMediatorQque.fullSector => Physics.SeparatedMediatorQque.fullSector,
  GUT.SeparatedMediatorQque.leftCore => Physics.SeparatedMediatorQque.leftCore,
  GUT.SeparatedMediatorQque.nonzero_of_source => Physics.SeparatedMediatorQque.nonzero_of_source,
  GUT.SeparatedMediatorQque.observer_coefficient_eq => Physics.SeparatedMediatorQque.observer_coefficient_eq,
  GUT.SeparatedMediatorQque.rightCore => Physics.SeparatedMediatorQque.rightCore,
  GUT.SeparatedMediatorQque.sector_eq_of_observer => Physics.SeparatedMediatorQque.sector_eq_of_observer,
  GUT.SeparatedMediatorQque.sector_eq_of_source => Physics.SeparatedMediatorQque.sector_eq_of_source,
  GUT.SeparatedMediatorQque.source_coefficient_eq => Physics.SeparatedMediatorQque.source_coefficient_eq
]

assert_compatible GUT.SeparatedMediatorQque.coreSector => Physics.SeparatedMediatorQque.coreSector
assert_compatible GUT.SeparatedMediatorQque.fullSector => Physics.SeparatedMediatorQque.fullSector
assert_compatible GUT.SeparatedMediatorQque.leftCore => Physics.SeparatedMediatorQque.leftCore
assert_compatible GUT.SeparatedMediatorQque.nonzero_of_source => Physics.SeparatedMediatorQque.nonzero_of_source
assert_compatible GUT.SeparatedMediatorQque.observer_coefficient_eq => Physics.SeparatedMediatorQque.observer_coefficient_eq
assert_compatible GUT.SeparatedMediatorQque.rightCore => Physics.SeparatedMediatorQque.rightCore
assert_compatible GUT.SeparatedMediatorQque.sector_eq_of_observer => Physics.SeparatedMediatorQque.sector_eq_of_observer
assert_compatible GUT.SeparatedMediatorQque.sector_eq_of_source => Physics.SeparatedMediatorQque.sector_eq_of_source
assert_compatible GUT.SeparatedMediatorQque.source_coefficient_eq => Physics.SeparatedMediatorQque.source_coefficient_eq
