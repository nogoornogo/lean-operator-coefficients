import Physics.StandardModel.Operators.Selection.AbelianProtonCharge
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.Selection.AbelianProtonCharge instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.StandardBranchProtonObstruction.Charges => Physics.StandardBranchProtonObstruction.Charges,
  GUT.StandardBranchProtonObstruction.Charges.casesOn => Physics.StandardBranchProtonObstruction.Charges.casesOn,
  GUT.StandardBranchProtonObstruction.Charges.ctorIdx => Physics.StandardBranchProtonObstruction.Charges.ctorIdx,
  GUT.StandardBranchProtonObstruction.Charges.down => Physics.StandardBranchProtonObstruction.Charges.down,
  GUT.StandardBranchProtonObstruction.Charges.electron => Physics.StandardBranchProtonObstruction.Charges.electron,
  GUT.StandardBranchProtonObstruction.Charges.ext => Physics.StandardBranchProtonObstruction.Charges.ext,
  GUT.StandardBranchProtonObstruction.Charges.ext_iff => Physics.StandardBranchProtonObstruction.Charges.ext_iff,
  GUT.StandardBranchProtonObstruction.Charges.lepton => Physics.StandardBranchProtonObstruction.Charges.lepton,
  GUT.StandardBranchProtonObstruction.Charges.mk => Physics.StandardBranchProtonObstruction.Charges.mk,
  GUT.StandardBranchProtonObstruction.Charges.mk.inj => Physics.StandardBranchProtonObstruction.Charges.mk.inj,
  GUT.StandardBranchProtonObstruction.Charges.mk.injEq => Physics.StandardBranchProtonObstruction.Charges.mk.injEq,
  GUT.StandardBranchProtonObstruction.Charges.mk.noConfusion => Physics.StandardBranchProtonObstruction.Charges.mk.noConfusion,
  GUT.StandardBranchProtonObstruction.Charges.mk.sizeOf_spec => Physics.StandardBranchProtonObstruction.Charges.mk.sizeOf_spec,
  GUT.StandardBranchProtonObstruction.Charges.noConfusion => Physics.StandardBranchProtonObstruction.Charges.noConfusion,
  GUT.StandardBranchProtonObstruction.Charges.noConfusionType => Physics.StandardBranchProtonObstruction.Charges.noConfusionType,
  GUT.StandardBranchProtonObstruction.Charges.quark => Physics.StandardBranchProtonObstruction.Charges.quark,
  GUT.StandardBranchProtonObstruction.Charges.rec => Physics.StandardBranchProtonObstruction.Charges.rec,
  GUT.StandardBranchProtonObstruction.Charges.recOn => Physics.StandardBranchProtonObstruction.Charges.recOn,
  GUT.StandardBranchProtonObstruction.Charges.up => Physics.StandardBranchProtonObstruction.Charges.up,
  GUT.StandardBranchProtonObstruction.SU5OrbitCompatible => Physics.StandardBranchProtonObstruction.SU5OrbitCompatible,
  GUT.StandardBranchProtonObstruction.protonFirst => Physics.StandardBranchProtonObstruction.protonFirst,
  GUT.StandardBranchProtonObstruction.protonFirst.eq_1 => Physics.StandardBranchProtonObstruction.protonFirst.eq_1,
  GUT.StandardBranchProtonObstruction.protonSecond => Physics.StandardBranchProtonObstruction.protonSecond,
  GUT.StandardBranchProtonObstruction.protonSecond.eq_1 => Physics.StandardBranchProtonObstruction.protonSecond.eq_1,
  GUT.StandardBranchProtonObstruction.proton_functionals_eq_zero_of_su5OrbitCompatible => Physics.StandardBranchProtonObstruction.proton_functionals_eq_zero_of_su5OrbitCompatible
]

assert_compatible GUT.StandardBranchProtonObstruction.Charges => Physics.StandardBranchProtonObstruction.Charges
assert_compatible GUT.StandardBranchProtonObstruction.Charges.casesOn => Physics.StandardBranchProtonObstruction.Charges.casesOn
assert_compatible GUT.StandardBranchProtonObstruction.Charges.ctorIdx => Physics.StandardBranchProtonObstruction.Charges.ctorIdx
assert_compatible GUT.StandardBranchProtonObstruction.Charges.down => Physics.StandardBranchProtonObstruction.Charges.down
assert_compatible GUT.StandardBranchProtonObstruction.Charges.electron => Physics.StandardBranchProtonObstruction.Charges.electron
assert_compatible GUT.StandardBranchProtonObstruction.Charges.ext => Physics.StandardBranchProtonObstruction.Charges.ext
assert_compatible GUT.StandardBranchProtonObstruction.Charges.ext_iff => Physics.StandardBranchProtonObstruction.Charges.ext_iff
assert_compatible GUT.StandardBranchProtonObstruction.Charges.lepton => Physics.StandardBranchProtonObstruction.Charges.lepton
assert_compatible GUT.StandardBranchProtonObstruction.Charges.mk => Physics.StandardBranchProtonObstruction.Charges.mk
assert_compatible GUT.StandardBranchProtonObstruction.Charges.mk.inj => Physics.StandardBranchProtonObstruction.Charges.mk.inj
assert_compatible GUT.StandardBranchProtonObstruction.Charges.mk.injEq => Physics.StandardBranchProtonObstruction.Charges.mk.injEq
assert_compatible GUT.StandardBranchProtonObstruction.Charges.mk.noConfusion => Physics.StandardBranchProtonObstruction.Charges.mk.noConfusion
assert_compatible GUT.StandardBranchProtonObstruction.Charges.mk.sizeOf_spec => Physics.StandardBranchProtonObstruction.Charges.mk.sizeOf_spec
assert_compatible GUT.StandardBranchProtonObstruction.Charges.noConfusion => Physics.StandardBranchProtonObstruction.Charges.noConfusion
assert_compatible GUT.StandardBranchProtonObstruction.Charges.noConfusionType => Physics.StandardBranchProtonObstruction.Charges.noConfusionType
assert_compatible GUT.StandardBranchProtonObstruction.Charges.quark => Physics.StandardBranchProtonObstruction.Charges.quark
assert_compatible GUT.StandardBranchProtonObstruction.Charges.rec => Physics.StandardBranchProtonObstruction.Charges.rec
assert_compatible GUT.StandardBranchProtonObstruction.Charges.recOn => Physics.StandardBranchProtonObstruction.Charges.recOn
assert_compatible GUT.StandardBranchProtonObstruction.Charges.up => Physics.StandardBranchProtonObstruction.Charges.up
assert_compatible GUT.StandardBranchProtonObstruction.SU5OrbitCompatible => Physics.StandardBranchProtonObstruction.SU5OrbitCompatible
assert_compatible GUT.StandardBranchProtonObstruction.protonFirst => Physics.StandardBranchProtonObstruction.protonFirst
assert_compatible GUT.StandardBranchProtonObstruction.protonFirst.eq_1 => Physics.StandardBranchProtonObstruction.protonFirst.eq_1
assert_compatible GUT.StandardBranchProtonObstruction.protonSecond => Physics.StandardBranchProtonObstruction.protonSecond
assert_compatible GUT.StandardBranchProtonObstruction.protonSecond.eq_1 => Physics.StandardBranchProtonObstruction.protonSecond.eq_1
assert_compatible GUT.StandardBranchProtonObstruction.proton_functionals_eq_zero_of_su5OrbitCompatible => Physics.StandardBranchProtonObstruction.proton_functionals_eq_zero_of_su5OrbitCompatible
