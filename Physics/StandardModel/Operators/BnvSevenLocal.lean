import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenLocal
import Physics.StandardModel.Gauge.DipoleGaugeTensor
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Physics.StandardModel.Operators.DuqlOrderedCompleteness
import Physics.StandardModel.Operators.FourWeakWeylCompleteness
import Math.RepresentationTheory.FiniteLocalRelationCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenLocal instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BnvSevenLocal.LocalCoefficient => Physics.BnvSevenLocal.LocalCoefficient,
  GUT.BnvSevenLocal.colorPairing => Physics.BnvSevenLocal.colorPairing,
  GUT.BnvSevenLocal.colorPairing.eq_1 => Physics.BnvSevenLocal.colorPairing.eq_1,
  GUT.BnvSevenLocal.colorProbe => Physics.BnvSevenLocal.colorProbe,
  GUT.BnvSevenLocal.colorProbe.eq_1 => Physics.BnvSevenLocal.colorProbe.eq_1,
  GUT.BnvSevenLocal.colorRepresentation => Physics.BnvSevenLocal.colorRepresentation,
  GUT.BnvSevenLocal.color_unique => Physics.BnvSevenLocal.color_unique,
  GUT.BnvSevenLocal.coordinates => Physics.BnvSevenLocal.coordinates,
  GUT.BnvSevenLocal.fourWeakGaugePairing => Physics.BnvSevenLocal.fourWeakGaugePairing,
  GUT.BnvSevenLocal.fourWeakGaugeProbe => Physics.BnvSevenLocal.fourWeakGaugeProbe,
  GUT.BnvSevenLocal.fourWeakGaugeRepresentation => Physics.BnvSevenLocal.fourWeakGaugeRepresentation,
  GUT.BnvSevenLocal.fourWeakGauge_reconstruction => Physics.BnvSevenLocal.fourWeakGauge_reconstruction,
  GUT.BnvSevenLocal.gaugePairing => Physics.BnvSevenLocal.gaugePairing,
  GUT.BnvSevenLocal.gaugeProbe => Physics.BnvSevenLocal.gaugeProbe,
  GUT.BnvSevenLocal.gaugeRepresentation => Physics.BnvSevenLocal.gaugeRepresentation,
  GUT.BnvSevenLocal.gauge_normalized => Physics.BnvSevenLocal.gauge_normalized,
  GUT.BnvSevenLocal.gauge_unique => Physics.BnvSevenLocal.gauge_unique,
  GUT.BnvSevenLocal.mixedFlavorEquiv => Physics.BnvSevenLocal.mixedFlavorEquiv,
  GUT.BnvSevenLocal.mixedFourWeakFlavorEquiv => Physics.BnvSevenLocal.mixedFourWeakFlavorEquiv,
  GUT.BnvSevenLocal.mixedFourWeakPairing => Physics.BnvSevenLocal.mixedFourWeakPairing,
  GUT.BnvSevenLocal.mixedFourWeakProbe => Physics.BnvSevenLocal.mixedFourWeakProbe,
  GUT.BnvSevenLocal.mixedFourWeakRepresentation => Physics.BnvSevenLocal.mixedFourWeakRepresentation,
  GUT.BnvSevenLocal.mixedFourWeakStatisticsEquiv => Physics.BnvSevenLocal.mixedFourWeakStatisticsEquiv,
  GUT.BnvSevenLocal.mixedFourWeak_pairing_probe => Physics.BnvSevenLocal.mixedFourWeak_pairing_probe,
  GUT.BnvSevenLocal.mixedFourWeak_reconstruction => Physics.BnvSevenLocal.mixedFourWeak_reconstruction,
  GUT.BnvSevenLocal.mixedPairing => Physics.BnvSevenLocal.mixedPairing,
  GUT.BnvSevenLocal.mixedProbe => Physics.BnvSevenLocal.mixedProbe,
  GUT.BnvSevenLocal.mixedRepresentation => Physics.BnvSevenLocal.mixedRepresentation,
  GUT.BnvSevenLocal.mixed_normalized => Physics.BnvSevenLocal.mixed_normalized,
  GUT.BnvSevenLocal.mixed_unique => Physics.BnvSevenLocal.mixed_unique,
  GUT.BnvSevenLocal.pairing => Physics.BnvSevenLocal.pairing,
  GUT.BnvSevenLocal.pairing_probe => Physics.BnvSevenLocal.pairing_probe,
  GUT.BnvSevenLocal.probe => Physics.BnvSevenLocal.probe,
  GUT.BnvSevenLocal.reconstruction => Physics.BnvSevenLocal.reconstruction,
  GUT.BnvSevenLocal.representation => Physics.BnvSevenLocal.representation,
  GUT.BnvSevenLocal.sameFlavorEquiv => Physics.BnvSevenLocal.sameFlavorEquiv,
  GUT.BnvSevenLocal.sameStatisticsEquiv => Physics.BnvSevenLocal.sameStatisticsEquiv,
  GUT.BnvSevenLocal.spin_normalized => Physics.BnvSevenLocal.spin_normalized
]

assert_compatible GUT.BnvSevenLocal.LocalCoefficient => Physics.BnvSevenLocal.LocalCoefficient
assert_compatible GUT.BnvSevenLocal.colorPairing => Physics.BnvSevenLocal.colorPairing
assert_compatible GUT.BnvSevenLocal.colorPairing.eq_1 => Physics.BnvSevenLocal.colorPairing.eq_1
assert_compatible GUT.BnvSevenLocal.colorProbe => Physics.BnvSevenLocal.colorProbe
assert_compatible GUT.BnvSevenLocal.colorProbe.eq_1 => Physics.BnvSevenLocal.colorProbe.eq_1
assert_compatible GUT.BnvSevenLocal.colorRepresentation => Physics.BnvSevenLocal.colorRepresentation
assert_compatible GUT.BnvSevenLocal.color_unique => Physics.BnvSevenLocal.color_unique
assert_compatible GUT.BnvSevenLocal.coordinates => Physics.BnvSevenLocal.coordinates
assert_compatible GUT.BnvSevenLocal.fourWeakGaugePairing => Physics.BnvSevenLocal.fourWeakGaugePairing
assert_compatible GUT.BnvSevenLocal.fourWeakGaugeProbe => Physics.BnvSevenLocal.fourWeakGaugeProbe
assert_compatible GUT.BnvSevenLocal.fourWeakGaugeRepresentation => Physics.BnvSevenLocal.fourWeakGaugeRepresentation
assert_compatible GUT.BnvSevenLocal.fourWeakGauge_reconstruction => Physics.BnvSevenLocal.fourWeakGauge_reconstruction
assert_compatible GUT.BnvSevenLocal.gaugePairing => Physics.BnvSevenLocal.gaugePairing
assert_compatible GUT.BnvSevenLocal.gaugeProbe => Physics.BnvSevenLocal.gaugeProbe
assert_compatible GUT.BnvSevenLocal.gaugeRepresentation => Physics.BnvSevenLocal.gaugeRepresentation
assert_compatible GUT.BnvSevenLocal.gauge_normalized => Physics.BnvSevenLocal.gauge_normalized
assert_compatible GUT.BnvSevenLocal.gauge_unique => Physics.BnvSevenLocal.gauge_unique
assert_compatible GUT.BnvSevenLocal.mixedFlavorEquiv => Physics.BnvSevenLocal.mixedFlavorEquiv
assert_compatible GUT.BnvSevenLocal.mixedFourWeakFlavorEquiv => Physics.BnvSevenLocal.mixedFourWeakFlavorEquiv
assert_compatible GUT.BnvSevenLocal.mixedFourWeakPairing => Physics.BnvSevenLocal.mixedFourWeakPairing
assert_compatible GUT.BnvSevenLocal.mixedFourWeakProbe => Physics.BnvSevenLocal.mixedFourWeakProbe
assert_compatible GUT.BnvSevenLocal.mixedFourWeakRepresentation => Physics.BnvSevenLocal.mixedFourWeakRepresentation
assert_compatible GUT.BnvSevenLocal.mixedFourWeakStatisticsEquiv => Physics.BnvSevenLocal.mixedFourWeakStatisticsEquiv
assert_compatible GUT.BnvSevenLocal.mixedFourWeak_pairing_probe => Physics.BnvSevenLocal.mixedFourWeak_pairing_probe
assert_compatible GUT.BnvSevenLocal.mixedFourWeak_reconstruction => Physics.BnvSevenLocal.mixedFourWeak_reconstruction
assert_compatible GUT.BnvSevenLocal.mixedPairing => Physics.BnvSevenLocal.mixedPairing
assert_compatible GUT.BnvSevenLocal.mixedProbe => Physics.BnvSevenLocal.mixedProbe
assert_compatible GUT.BnvSevenLocal.mixedRepresentation => Physics.BnvSevenLocal.mixedRepresentation
assert_compatible GUT.BnvSevenLocal.mixed_normalized => Physics.BnvSevenLocal.mixed_normalized
assert_compatible GUT.BnvSevenLocal.mixed_unique => Physics.BnvSevenLocal.mixed_unique
assert_compatible GUT.BnvSevenLocal.pairing => Physics.BnvSevenLocal.pairing
assert_compatible GUT.BnvSevenLocal.pairing_probe => Physics.BnvSevenLocal.pairing_probe
assert_compatible GUT.BnvSevenLocal.probe => Physics.BnvSevenLocal.probe
assert_compatible GUT.BnvSevenLocal.reconstruction => Physics.BnvSevenLocal.reconstruction
assert_compatible GUT.BnvSevenLocal.representation => Physics.BnvSevenLocal.representation
assert_compatible GUT.BnvSevenLocal.sameFlavorEquiv => Physics.BnvSevenLocal.sameFlavorEquiv
assert_compatible GUT.BnvSevenLocal.sameStatisticsEquiv => Physics.BnvSevenLocal.sameStatisticsEquiv
assert_compatible GUT.BnvSevenLocal.spin_normalized => Physics.BnvSevenLocal.spin_normalized
