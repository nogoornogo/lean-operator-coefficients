import Physics.StandardModel.Operators.Support.Coordinates.SMGaussianLocalData
import Physics.StandardModel.Operators.SMRationalLocalKernel
import Math.RepresentationTheory.GaussianCompactTests
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Support.Coordinates.SMGaussianLocalData instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.SMGaussianLocalData.Data => Physics.SMGaussianLocalData.Data,
  GUT.SMGaussianLocalData.Data.casesOn => Physics.SMGaussianLocalData.Data.casesOn,
  GUT.SMGaussianLocalData.Data.color => Physics.SMGaussianLocalData.Data.color,
  GUT.SMGaussianLocalData.Data.ctorIdx => Physics.SMGaussianLocalData.Data.ctorIdx,
  GUT.SMGaussianLocalData.Data.mk => Physics.SMGaussianLocalData.Data.mk,
  GUT.SMGaussianLocalData.Data.mk.inj => Physics.SMGaussianLocalData.Data.mk.inj,
  GUT.SMGaussianLocalData.Data.mk.injEq => Physics.SMGaussianLocalData.Data.mk.injEq,
  GUT.SMGaussianLocalData.Data.mk.noConfusion => Physics.SMGaussianLocalData.Data.mk.noConfusion,
  GUT.SMGaussianLocalData.Data.mk.sizeOf_spec => Physics.SMGaussianLocalData.Data.mk.sizeOf_spec,
  GUT.SMGaussianLocalData.Data.noConfusion => Physics.SMGaussianLocalData.Data.noConfusion,
  GUT.SMGaussianLocalData.Data.noConfusionType => Physics.SMGaussianLocalData.Data.noConfusionType,
  GUT.SMGaussianLocalData.Data.phase => Physics.SMGaussianLocalData.Data.phase,
  GUT.SMGaussianLocalData.Data.rec => Physics.SMGaussianLocalData.Data.rec,
  GUT.SMGaussianLocalData.Data.recOn => Physics.SMGaussianLocalData.Data.recOn,
  GUT.SMGaussianLocalData.Data.spin => Physics.SMGaussianLocalData.Data.spin,
  GUT.SMGaussianLocalData.Data.weak => Physics.SMGaussianLocalData.Data.weak,
  GUT.SMGaussianLocalData.K => Physics.SMGaussianLocalData.K,
  GUT.SMGaussianLocalData.color_embed => Physics.SMGaussianLocalData.color_embed,
  GUT.SMGaussianLocalData.data => Physics.SMGaussianLocalData.data,
  GUT.SMGaussianLocalData.data.eq_1 => Physics.SMGaussianLocalData.data.eq_1,
  GUT.SMGaussianLocalData.data.eq_2 => Physics.SMGaussianLocalData.data.eq_2,
  GUT.SMGaussianLocalData.data.eq_3 => Physics.SMGaussianLocalData.data.eq_3,
  GUT.SMGaussianLocalData.data.eq_4 => Physics.SMGaussianLocalData.data.eq_4,
  GUT.SMGaussianLocalData.phase_embed => Physics.SMGaussianLocalData.phase_embed,
  GUT.SMGaussianLocalData.spinSample => Physics.SMGaussianLocalData.spinSample,
  GUT.SMGaussianLocalData.spin_data_embed => Physics.SMGaussianLocalData.spin_data_embed,
  GUT.SMGaussianLocalData.spin_embed => Physics.SMGaussianLocalData.spin_embed,
  GUT.SMGaussianLocalData.weak_embed => Physics.SMGaussianLocalData.weak_embed,
  GUT.SMRationalLocalKernel.tests.eq_1 => Physics.SMRationalLocalKernel.tests.eq_1,
  GUT.SMRationalLocalKernel.tests.eq_2 => Physics.SMRationalLocalKernel.tests.eq_2,
  GUT.SMRationalLocalKernel.tests.eq_3 => Physics.SMRationalLocalKernel.tests.eq_3,
  GUT.SMRationalLocalKernel.tests.eq_4 => Physics.SMRationalLocalKernel.tests.eq_4
]

assert_compatible GUT.SMGaussianLocalData.Data => Physics.SMGaussianLocalData.Data
assert_compatible GUT.SMGaussianLocalData.Data.casesOn => Physics.SMGaussianLocalData.Data.casesOn
assert_compatible GUT.SMGaussianLocalData.Data.color => Physics.SMGaussianLocalData.Data.color
assert_compatible GUT.SMGaussianLocalData.Data.ctorIdx => Physics.SMGaussianLocalData.Data.ctorIdx
assert_compatible GUT.SMGaussianLocalData.Data.mk => Physics.SMGaussianLocalData.Data.mk
assert_compatible GUT.SMGaussianLocalData.Data.mk.inj => Physics.SMGaussianLocalData.Data.mk.inj
assert_compatible GUT.SMGaussianLocalData.Data.mk.injEq => Physics.SMGaussianLocalData.Data.mk.injEq
assert_compatible GUT.SMGaussianLocalData.Data.mk.noConfusion => Physics.SMGaussianLocalData.Data.mk.noConfusion
assert_compatible GUT.SMGaussianLocalData.Data.mk.sizeOf_spec => Physics.SMGaussianLocalData.Data.mk.sizeOf_spec
assert_compatible GUT.SMGaussianLocalData.Data.noConfusion => Physics.SMGaussianLocalData.Data.noConfusion
assert_compatible GUT.SMGaussianLocalData.Data.noConfusionType => Physics.SMGaussianLocalData.Data.noConfusionType
assert_compatible GUT.SMGaussianLocalData.Data.phase => Physics.SMGaussianLocalData.Data.phase
assert_compatible GUT.SMGaussianLocalData.Data.rec => Physics.SMGaussianLocalData.Data.rec
assert_compatible GUT.SMGaussianLocalData.Data.recOn => Physics.SMGaussianLocalData.Data.recOn
assert_compatible GUT.SMGaussianLocalData.Data.spin => Physics.SMGaussianLocalData.Data.spin
assert_compatible GUT.SMGaussianLocalData.Data.weak => Physics.SMGaussianLocalData.Data.weak
assert_compatible GUT.SMGaussianLocalData.K => Physics.SMGaussianLocalData.K
assert_compatible GUT.SMGaussianLocalData.color_embed => Physics.SMGaussianLocalData.color_embed
assert_compatible GUT.SMGaussianLocalData.data => Physics.SMGaussianLocalData.data
assert_compatible GUT.SMGaussianLocalData.data.eq_1 => Physics.SMGaussianLocalData.data.eq_1
assert_compatible GUT.SMGaussianLocalData.data.eq_2 => Physics.SMGaussianLocalData.data.eq_2
assert_compatible GUT.SMGaussianLocalData.data.eq_3 => Physics.SMGaussianLocalData.data.eq_3
assert_compatible GUT.SMGaussianLocalData.data.eq_4 => Physics.SMGaussianLocalData.data.eq_4
assert_compatible GUT.SMGaussianLocalData.phase_embed => Physics.SMGaussianLocalData.phase_embed
assert_compatible GUT.SMGaussianLocalData.spinSample => Physics.SMGaussianLocalData.spinSample
assert_compatible GUT.SMGaussianLocalData.spin_data_embed => Physics.SMGaussianLocalData.spin_data_embed
assert_compatible GUT.SMGaussianLocalData.spin_embed => Physics.SMGaussianLocalData.spin_embed
assert_compatible GUT.SMGaussianLocalData.weak_embed => Physics.SMGaussianLocalData.weak_embed
assert_compatible GUT.SMRationalLocalKernel.tests.eq_1 => Physics.SMRationalLocalKernel.tests.eq_1
assert_compatible GUT.SMRationalLocalKernel.tests.eq_2 => Physics.SMRationalLocalKernel.tests.eq_2
assert_compatible GUT.SMRationalLocalKernel.tests.eq_3 => Physics.SMRationalLocalKernel.tests.eq_3
assert_compatible GUT.SMRationalLocalKernel.tests.eq_4 => Physics.SMRationalLocalKernel.tests.eq_4
