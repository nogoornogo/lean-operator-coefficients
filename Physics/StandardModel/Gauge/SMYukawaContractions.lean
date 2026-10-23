import Physics.StandardModel.Gauge.Tensors.SMYukawaContractions
import Physics.StandardModel.Gauge.WeakContragredient
import Physics.StandardModel.Gauge.HyperchargeTensorTransport
import Math.RepresentationTheory.InvariantPairing
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Gauge.Tensors.SMYukawaContractions instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMYukawaContractions.antiHiggs => Physics.SMYukawaContractions.antiHiggs,
  GUT.SMYukawaContractions.colorCovector => Physics.SMYukawaContractions.colorCovector,
  GUT.SMYukawaContractions.colorCovector.eq_1 => Physics.SMYukawaContractions.colorCovector.eq_1,
  GUT.SMYukawaContractions.downGauge => Physics.SMYukawaContractions.downGauge,
  GUT.SMYukawaContractions.downGauge.eq_1 => Physics.SMYukawaContractions.downGauge.eq_1,
  GUT.SMYukawaContractions.downLinear => Physics.SMYukawaContractions.downLinear,
  GUT.SMYukawaContractions.downLinear.eq_1 => Physics.SMYukawaContractions.downLinear.eq_1,
  GUT.SMYukawaContractions.downLinear_tmul => Physics.SMYukawaContractions.downLinear_tmul,
  GUT.SMYukawaContractions.downMap => Physics.SMYukawaContractions.downMap,
  GUT.SMYukawaContractions.downMap.eq_1 => Physics.SMYukawaContractions.downMap.eq_1,
  GUT.SMYukawaContractions.downOrdered => Physics.SMYukawaContractions.downOrdered,
  GUT.SMYukawaContractions.downOrdered_apply => Physics.SMYukawaContractions.downOrdered_apply,
  GUT.SMYukawaContractions.down_witness => Physics.SMYukawaContractions.down_witness,
  GUT.SMYukawaContractions.electronGauge => Physics.SMYukawaContractions.electronGauge,
  GUT.SMYukawaContractions.electronGauge.eq_1 => Physics.SMYukawaContractions.electronGauge.eq_1,
  GUT.SMYukawaContractions.electronMap => Physics.SMYukawaContractions.electronMap,
  GUT.SMYukawaContractions.electronMap.eq_1 => Physics.SMYukawaContractions.electronMap.eq_1,
  GUT.SMYukawaContractions.electronOrdered => Physics.SMYukawaContractions.electronOrdered,
  GUT.SMYukawaContractions.electronOrdered_apply => Physics.SMYukawaContractions.electronOrdered_apply,
  GUT.SMYukawaContractions.electron_witness => Physics.SMYukawaContractions.electron_witness,
  GUT.SMYukawaContractions.higgs => Physics.SMYukawaContractions.higgs,
  GUT.SMYukawaContractions.instAddCommGroupQuark => Physics.SMYukawaContractions.instAddCommGroupQuark,
  GUT.SMYukawaContractions.lineCovector => Physics.SMYukawaContractions.lineCovector,
  GUT.SMYukawaContractions.lineCovector.eq_1 => Physics.SMYukawaContractions.lineCovector.eq_1,
  GUT.SMYukawaContractions.swapLast => Physics.SMYukawaContractions.swapLast,
  GUT.SMYukawaContractions.upGauge => Physics.SMYukawaContractions.upGauge,
  GUT.SMYukawaContractions.upGauge.eq_1 => Physics.SMYukawaContractions.upGauge.eq_1,
  GUT.SMYukawaContractions.upLinear => Physics.SMYukawaContractions.upLinear,
  GUT.SMYukawaContractions.upLinear.eq_1 => Physics.SMYukawaContractions.upLinear.eq_1,
  GUT.SMYukawaContractions.upLinear_tmul => Physics.SMYukawaContractions.upLinear_tmul,
  GUT.SMYukawaContractions.upMap => Physics.SMYukawaContractions.upMap,
  GUT.SMYukawaContractions.upMap.eq_1 => Physics.SMYukawaContractions.upMap.eq_1,
  GUT.SMYukawaContractions.upOrdered => Physics.SMYukawaContractions.upOrdered,
  GUT.SMYukawaContractions.upOrdered_apply => Physics.SMYukawaContractions.upOrdered_apply,
  GUT.SMYukawaContractions.up_witness => Physics.SMYukawaContractions.up_witness,
  GUT.SMYukawaContractions.weakCovector => Physics.SMYukawaContractions.weakCovector,
  GUT.SMYukawaContractions.weakCovector.eq_1 => Physics.SMYukawaContractions.weakCovector.eq_1
]

assert_compatible GUT.SMYukawaContractions.antiHiggs => Physics.SMYukawaContractions.antiHiggs
assert_compatible GUT.SMYukawaContractions.colorCovector => Physics.SMYukawaContractions.colorCovector
assert_compatible GUT.SMYukawaContractions.colorCovector.eq_1 => Physics.SMYukawaContractions.colorCovector.eq_1
assert_compatible GUT.SMYukawaContractions.downGauge => Physics.SMYukawaContractions.downGauge
assert_compatible GUT.SMYukawaContractions.downGauge.eq_1 => Physics.SMYukawaContractions.downGauge.eq_1
assert_compatible GUT.SMYukawaContractions.downLinear => Physics.SMYukawaContractions.downLinear
assert_compatible GUT.SMYukawaContractions.downLinear.eq_1 => Physics.SMYukawaContractions.downLinear.eq_1
assert_compatible GUT.SMYukawaContractions.downLinear_tmul => Physics.SMYukawaContractions.downLinear_tmul
assert_compatible GUT.SMYukawaContractions.downMap => Physics.SMYukawaContractions.downMap
assert_compatible GUT.SMYukawaContractions.downMap.eq_1 => Physics.SMYukawaContractions.downMap.eq_1
assert_compatible GUT.SMYukawaContractions.downOrdered => Physics.SMYukawaContractions.downOrdered
assert_compatible GUT.SMYukawaContractions.downOrdered_apply => Physics.SMYukawaContractions.downOrdered_apply
assert_compatible GUT.SMYukawaContractions.down_witness => Physics.SMYukawaContractions.down_witness
assert_compatible GUT.SMYukawaContractions.electronGauge => Physics.SMYukawaContractions.electronGauge
assert_compatible GUT.SMYukawaContractions.electronGauge.eq_1 => Physics.SMYukawaContractions.electronGauge.eq_1
assert_compatible GUT.SMYukawaContractions.electronMap => Physics.SMYukawaContractions.electronMap
assert_compatible GUT.SMYukawaContractions.electronMap.eq_1 => Physics.SMYukawaContractions.electronMap.eq_1
assert_compatible GUT.SMYukawaContractions.electronOrdered => Physics.SMYukawaContractions.electronOrdered
assert_compatible GUT.SMYukawaContractions.electronOrdered_apply => Physics.SMYukawaContractions.electronOrdered_apply
assert_compatible GUT.SMYukawaContractions.electron_witness => Physics.SMYukawaContractions.electron_witness
assert_compatible GUT.SMYukawaContractions.higgs => Physics.SMYukawaContractions.higgs
assert_compatible GUT.SMYukawaContractions.instAddCommGroupQuark => Physics.SMYukawaContractions.instAddCommGroupQuark
assert_compatible GUT.SMYukawaContractions.lineCovector => Physics.SMYukawaContractions.lineCovector
assert_compatible GUT.SMYukawaContractions.lineCovector.eq_1 => Physics.SMYukawaContractions.lineCovector.eq_1
assert_compatible GUT.SMYukawaContractions.swapLast => Physics.SMYukawaContractions.swapLast
assert_compatible GUT.SMYukawaContractions.upGauge => Physics.SMYukawaContractions.upGauge
assert_compatible GUT.SMYukawaContractions.upGauge.eq_1 => Physics.SMYukawaContractions.upGauge.eq_1
assert_compatible GUT.SMYukawaContractions.upLinear => Physics.SMYukawaContractions.upLinear
assert_compatible GUT.SMYukawaContractions.upLinear.eq_1 => Physics.SMYukawaContractions.upLinear.eq_1
assert_compatible GUT.SMYukawaContractions.upLinear_tmul => Physics.SMYukawaContractions.upLinear_tmul
assert_compatible GUT.SMYukawaContractions.upMap => Physics.SMYukawaContractions.upMap
assert_compatible GUT.SMYukawaContractions.upMap.eq_1 => Physics.SMYukawaContractions.upMap.eq_1
assert_compatible GUT.SMYukawaContractions.upOrdered => Physics.SMYukawaContractions.upOrdered
assert_compatible GUT.SMYukawaContractions.upOrdered_apply => Physics.SMYukawaContractions.upOrdered_apply
assert_compatible GUT.SMYukawaContractions.up_witness => Physics.SMYukawaContractions.up_witness
assert_compatible GUT.SMYukawaContractions.weakCovector => Physics.SMYukawaContractions.weakCovector
assert_compatible GUT.SMYukawaContractions.weakCovector.eq_1 => Physics.SMYukawaContractions.weakCovector.eq_1
