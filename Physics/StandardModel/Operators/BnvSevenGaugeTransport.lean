import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenGaugeTransport
import Physics.StandardModel.Gauge.HyperchargeTensorTransport
import Physics.StandardModel.Gauge.WeakContragredient
import Physics.StandardModel.Operators.BnvSevenLocal
import Math.RepresentationTheory.InvariantCoefficientTransport
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenGaugeTransport instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenGaugeTransport.antiElectron => Physics.BnvSevenGaugeTransport.antiElectron,
  GUT.BnvSevenGaugeTransport.antiHiggs => Physics.BnvSevenGaugeTransport.antiHiggs,
  GUT.BnvSevenGaugeTransport.antiLepton => Physics.BnvSevenGaugeTransport.antiLepton,
  GUT.BnvSevenGaugeTransport.core => Physics.BnvSevenGaugeTransport.core,
  GUT.BnvSevenGaugeTransport.cover => Physics.BnvSevenGaugeTransport.cover,
  GUT.BnvSevenGaugeTransport.cover_surjective => Physics.BnvSevenGaugeTransport.cover_surjective,
  GUT.BnvSevenGaugeTransport.ddd => Physics.BnvSevenGaugeTransport.ddd,
  GUT.BnvSevenGaugeTransport.dddCore => Physics.BnvSevenGaugeTransport.dddCore,
  GUT.BnvSevenGaugeTransport.dddInvariantEquiv => Physics.BnvSevenGaugeTransport.dddInvariantEquiv,
  GUT.BnvSevenGaugeTransport.dddPairing => Physics.BnvSevenGaugeTransport.dddPairing,
  GUT.BnvSevenGaugeTransport.dddProbe => Physics.BnvSevenGaugeTransport.dddProbe,
  GUT.BnvSevenGaugeTransport.dddRepresentation => Physics.BnvSevenGaugeTransport.dddRepresentation,
  GUT.BnvSevenGaugeTransport.ddd_unique => Physics.BnvSevenGaugeTransport.ddd_unique,
  GUT.BnvSevenGaugeTransport.fourWeakCore => Physics.BnvSevenGaugeTransport.fourWeakCore,
  GUT.BnvSevenGaugeTransport.fourWeakNeutral => Physics.BnvSevenGaugeTransport.fourWeakNeutral,
  GUT.BnvSevenGaugeTransport.moveWeak => Physics.BnvSevenGaugeTransport.moveWeak,
  GUT.BnvSevenGaugeTransport.neutralRepresentation => Physics.BnvSevenGaugeTransport.neutralRepresentation,
  GUT.BnvSevenGaugeTransport.qdd => Physics.BnvSevenGaugeTransport.qdd,
  GUT.BnvSevenGaugeTransport.qddCore => Physics.BnvSevenGaugeTransport.qddCore,
  GUT.BnvSevenGaugeTransport.qddInvariantEquiv => Physics.BnvSevenGaugeTransport.qddInvariantEquiv,
  GUT.BnvSevenGaugeTransport.qddNeutral => Physics.BnvSevenGaugeTransport.qddNeutral,
  GUT.BnvSevenGaugeTransport.qddPairing => Physics.BnvSevenGaugeTransport.qddPairing,
  GUT.BnvSevenGaugeTransport.qddProbe => Physics.BnvSevenGaugeTransport.qddProbe,
  GUT.BnvSevenGaugeTransport.qddRepresentation => Physics.BnvSevenGaugeTransport.qddRepresentation,
  GUT.BnvSevenGaugeTransport.qdd_unique => Physics.BnvSevenGaugeTransport.qdd_unique,
  GUT.BnvSevenGaugeTransport.qqd => Physics.BnvSevenGaugeTransport.qqd,
  GUT.BnvSevenGaugeTransport.qqdCore => Physics.BnvSevenGaugeTransport.qqdCore,
  GUT.BnvSevenGaugeTransport.qqdInvariantEquiv => Physics.BnvSevenGaugeTransport.qqdInvariantEquiv,
  GUT.BnvSevenGaugeTransport.qqdPairing => Physics.BnvSevenGaugeTransport.qqdPairing,
  GUT.BnvSevenGaugeTransport.qqdProbe => Physics.BnvSevenGaugeTransport.qqdProbe,
  GUT.BnvSevenGaugeTransport.qqdRepresentation => Physics.BnvSevenGaugeTransport.qqdRepresentation,
  GUT.BnvSevenGaugeTransport.qqd_reconstruction => Physics.BnvSevenGaugeTransport.qqd_reconstruction,
  GUT.BnvSevenGaugeTransport.regroup => Physics.BnvSevenGaugeTransport.regroup,
  GUT.BnvSevenGaugeTransport.regroupFourWeak => Physics.BnvSevenGaugeTransport.regroupFourWeak,
  GUT.BnvSevenGaugeTransport.regroupQdd => Physics.BnvSevenGaugeTransport.regroupQdd,
  GUT.BnvSevenGaugeTransport.udd => Physics.BnvSevenGaugeTransport.udd,
  GUT.BnvSevenGaugeTransport.uddCore => Physics.BnvSevenGaugeTransport.uddCore,
  GUT.BnvSevenGaugeTransport.uddInvariantEquiv => Physics.BnvSevenGaugeTransport.uddInvariantEquiv,
  GUT.BnvSevenGaugeTransport.uddPairing => Physics.BnvSevenGaugeTransport.uddPairing,
  GUT.BnvSevenGaugeTransport.uddProbe => Physics.BnvSevenGaugeTransport.uddProbe,
  GUT.BnvSevenGaugeTransport.uddRepresentation => Physics.BnvSevenGaugeTransport.uddRepresentation,
  GUT.BnvSevenGaugeTransport.udd_unique => Physics.BnvSevenGaugeTransport.udd_unique
]

assert_compatible GUT.BnvSevenGaugeTransport.antiElectron => Physics.BnvSevenGaugeTransport.antiElectron
assert_compatible GUT.BnvSevenGaugeTransport.antiHiggs => Physics.BnvSevenGaugeTransport.antiHiggs
assert_compatible GUT.BnvSevenGaugeTransport.antiLepton => Physics.BnvSevenGaugeTransport.antiLepton
assert_compatible GUT.BnvSevenGaugeTransport.core => Physics.BnvSevenGaugeTransport.core
assert_compatible GUT.BnvSevenGaugeTransport.cover => Physics.BnvSevenGaugeTransport.cover
assert_compatible GUT.BnvSevenGaugeTransport.cover_surjective => Physics.BnvSevenGaugeTransport.cover_surjective
assert_compatible GUT.BnvSevenGaugeTransport.ddd => Physics.BnvSevenGaugeTransport.ddd
assert_compatible GUT.BnvSevenGaugeTransport.dddCore => Physics.BnvSevenGaugeTransport.dddCore
assert_compatible GUT.BnvSevenGaugeTransport.dddInvariantEquiv => Physics.BnvSevenGaugeTransport.dddInvariantEquiv
assert_compatible GUT.BnvSevenGaugeTransport.dddPairing => Physics.BnvSevenGaugeTransport.dddPairing
assert_compatible GUT.BnvSevenGaugeTransport.dddProbe => Physics.BnvSevenGaugeTransport.dddProbe
assert_compatible GUT.BnvSevenGaugeTransport.dddRepresentation => Physics.BnvSevenGaugeTransport.dddRepresentation
assert_compatible GUT.BnvSevenGaugeTransport.ddd_unique => Physics.BnvSevenGaugeTransport.ddd_unique
assert_compatible GUT.BnvSevenGaugeTransport.fourWeakCore => Physics.BnvSevenGaugeTransport.fourWeakCore
assert_compatible GUT.BnvSevenGaugeTransport.fourWeakNeutral => Physics.BnvSevenGaugeTransport.fourWeakNeutral
assert_compatible GUT.BnvSevenGaugeTransport.moveWeak => Physics.BnvSevenGaugeTransport.moveWeak
assert_compatible GUT.BnvSevenGaugeTransport.neutralRepresentation => Physics.BnvSevenGaugeTransport.neutralRepresentation
assert_compatible GUT.BnvSevenGaugeTransport.qdd => Physics.BnvSevenGaugeTransport.qdd
assert_compatible GUT.BnvSevenGaugeTransport.qddCore => Physics.BnvSevenGaugeTransport.qddCore
assert_compatible GUT.BnvSevenGaugeTransport.qddInvariantEquiv => Physics.BnvSevenGaugeTransport.qddInvariantEquiv
assert_compatible GUT.BnvSevenGaugeTransport.qddNeutral => Physics.BnvSevenGaugeTransport.qddNeutral
assert_compatible GUT.BnvSevenGaugeTransport.qddPairing => Physics.BnvSevenGaugeTransport.qddPairing
assert_compatible GUT.BnvSevenGaugeTransport.qddProbe => Physics.BnvSevenGaugeTransport.qddProbe
assert_compatible GUT.BnvSevenGaugeTransport.qddRepresentation => Physics.BnvSevenGaugeTransport.qddRepresentation
assert_compatible GUT.BnvSevenGaugeTransport.qdd_unique => Physics.BnvSevenGaugeTransport.qdd_unique
assert_compatible GUT.BnvSevenGaugeTransport.qqd => Physics.BnvSevenGaugeTransport.qqd
assert_compatible GUT.BnvSevenGaugeTransport.qqdCore => Physics.BnvSevenGaugeTransport.qqdCore
assert_compatible GUT.BnvSevenGaugeTransport.qqdInvariantEquiv => Physics.BnvSevenGaugeTransport.qqdInvariantEquiv
assert_compatible GUT.BnvSevenGaugeTransport.qqdPairing => Physics.BnvSevenGaugeTransport.qqdPairing
assert_compatible GUT.BnvSevenGaugeTransport.qqdProbe => Physics.BnvSevenGaugeTransport.qqdProbe
assert_compatible GUT.BnvSevenGaugeTransport.qqdRepresentation => Physics.BnvSevenGaugeTransport.qqdRepresentation
assert_compatible GUT.BnvSevenGaugeTransport.qqd_reconstruction => Physics.BnvSevenGaugeTransport.qqd_reconstruction
assert_compatible GUT.BnvSevenGaugeTransport.regroup => Physics.BnvSevenGaugeTransport.regroup
assert_compatible GUT.BnvSevenGaugeTransport.regroupFourWeak => Physics.BnvSevenGaugeTransport.regroupFourWeak
assert_compatible GUT.BnvSevenGaugeTransport.regroupQdd => Physics.BnvSevenGaugeTransport.regroupQdd
assert_compatible GUT.BnvSevenGaugeTransport.udd => Physics.BnvSevenGaugeTransport.udd
assert_compatible GUT.BnvSevenGaugeTransport.uddCore => Physics.BnvSevenGaugeTransport.uddCore
assert_compatible GUT.BnvSevenGaugeTransport.uddInvariantEquiv => Physics.BnvSevenGaugeTransport.uddInvariantEquiv
assert_compatible GUT.BnvSevenGaugeTransport.uddPairing => Physics.BnvSevenGaugeTransport.uddPairing
assert_compatible GUT.BnvSevenGaugeTransport.uddProbe => Physics.BnvSevenGaugeTransport.uddProbe
assert_compatible GUT.BnvSevenGaugeTransport.uddRepresentation => Physics.BnvSevenGaugeTransport.uddRepresentation
assert_compatible GUT.BnvSevenGaugeTransport.udd_unique => Physics.BnvSevenGaugeTransport.udd_unique
