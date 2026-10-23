import Physics.StandardModel.Spectrum.Representations.BalancedSpeciesExtension
import Physics.StandardModel.Spectrum.ExactSMAutomaticPositive
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Spectrum.Representations.BalancedSpeciesExtension instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.BalancedSpeciesExtension.Extension => Physics.BalancedSpeciesExtension.Extension,
  GUT.BalancedSpeciesExtension.Extension.casesOn => Physics.BalancedSpeciesExtension.Extension.casesOn,
  GUT.BalancedSpeciesExtension.Extension.ctorIdx => Physics.BalancedSpeciesExtension.Extension.ctorIdx,
  GUT.BalancedSpeciesExtension.Extension.electron => Physics.BalancedSpeciesExtension.Extension.electron,
  GUT.BalancedSpeciesExtension.Extension.mk => Physics.BalancedSpeciesExtension.Extension.mk,
  GUT.BalancedSpeciesExtension.Extension.mk.inj => Physics.BalancedSpeciesExtension.Extension.mk.inj,
  GUT.BalancedSpeciesExtension.Extension.mk.injEq => Physics.BalancedSpeciesExtension.Extension.mk.injEq,
  GUT.BalancedSpeciesExtension.Extension.mk.noConfusion => Physics.BalancedSpeciesExtension.Extension.mk.noConfusion,
  GUT.BalancedSpeciesExtension.Extension.mk.sizeOf_spec => Physics.BalancedSpeciesExtension.Extension.mk.sizeOf_spec,
  GUT.BalancedSpeciesExtension.Extension.noConfusion => Physics.BalancedSpeciesExtension.Extension.noConfusion,
  GUT.BalancedSpeciesExtension.Extension.noConfusionType => Physics.BalancedSpeciesExtension.Extension.noConfusionType,
  GUT.BalancedSpeciesExtension.Extension.quark => Physics.BalancedSpeciesExtension.Extension.quark,
  GUT.BalancedSpeciesExtension.Extension.rec => Physics.BalancedSpeciesExtension.Extension.rec,
  GUT.BalancedSpeciesExtension.Extension.recOn => Physics.BalancedSpeciesExtension.Extension.recOn,
  GUT.BalancedSpeciesExtension.Extension.up => Physics.BalancedSpeciesExtension.Extension.up,
  GUT.BalancedSpeciesExtension.not_exact_of_quark_extra => Physics.BalancedSpeciesExtension.not_exact_of_quark_extra,
  GUT.BalancedSpeciesExtension.pairwise_positive => Physics.BalancedSpeciesExtension.pairwise_positive,
  GUT.BalancedSpeciesExtension.refl => Physics.BalancedSpeciesExtension.refl,
  GUT.BalancedSpeciesExtension.shared_positive => Physics.BalancedSpeciesExtension.shared_positive
]

assert_compatible GUT.BalancedSpeciesExtension.Extension => Physics.BalancedSpeciesExtension.Extension
assert_compatible GUT.BalancedSpeciesExtension.Extension.casesOn => Physics.BalancedSpeciesExtension.Extension.casesOn
assert_compatible GUT.BalancedSpeciesExtension.Extension.ctorIdx => Physics.BalancedSpeciesExtension.Extension.ctorIdx
assert_compatible GUT.BalancedSpeciesExtension.Extension.electron => Physics.BalancedSpeciesExtension.Extension.electron
assert_compatible GUT.BalancedSpeciesExtension.Extension.mk => Physics.BalancedSpeciesExtension.Extension.mk
assert_compatible GUT.BalancedSpeciesExtension.Extension.mk.inj => Physics.BalancedSpeciesExtension.Extension.mk.inj
assert_compatible GUT.BalancedSpeciesExtension.Extension.mk.injEq => Physics.BalancedSpeciesExtension.Extension.mk.injEq
assert_compatible GUT.BalancedSpeciesExtension.Extension.mk.noConfusion => Physics.BalancedSpeciesExtension.Extension.mk.noConfusion
assert_compatible GUT.BalancedSpeciesExtension.Extension.mk.sizeOf_spec => Physics.BalancedSpeciesExtension.Extension.mk.sizeOf_spec
assert_compatible GUT.BalancedSpeciesExtension.Extension.noConfusion => Physics.BalancedSpeciesExtension.Extension.noConfusion
assert_compatible GUT.BalancedSpeciesExtension.Extension.noConfusionType => Physics.BalancedSpeciesExtension.Extension.noConfusionType
assert_compatible GUT.BalancedSpeciesExtension.Extension.quark => Physics.BalancedSpeciesExtension.Extension.quark
assert_compatible GUT.BalancedSpeciesExtension.Extension.rec => Physics.BalancedSpeciesExtension.Extension.rec
assert_compatible GUT.BalancedSpeciesExtension.Extension.recOn => Physics.BalancedSpeciesExtension.Extension.recOn
assert_compatible GUT.BalancedSpeciesExtension.Extension.up => Physics.BalancedSpeciesExtension.Extension.up
assert_compatible GUT.BalancedSpeciesExtension.not_exact_of_quark_extra => Physics.BalancedSpeciesExtension.not_exact_of_quark_extra
assert_compatible GUT.BalancedSpeciesExtension.pairwise_positive => Physics.BalancedSpeciesExtension.pairwise_positive
assert_compatible GUT.BalancedSpeciesExtension.refl => Physics.BalancedSpeciesExtension.refl
assert_compatible GUT.BalancedSpeciesExtension.shared_positive => Physics.BalancedSpeciesExtension.shared_positive
