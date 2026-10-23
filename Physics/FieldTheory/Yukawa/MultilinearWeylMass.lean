import Physics.FieldTheory.Yukawa.Mass.MultilinearWeylMass
import Physics.FieldTheory.Yukawa.WeylMassFamily
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Yukawa.Mass.MultilinearWeylMass instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylMassFamily.EquivariantFamily.mk.congr_simp => Physics.WeylMassFamily.EquivariantFamily.mk.congr_simp,
  GUT.WeylMassFamily.EquivariantFamily.sum => Physics.WeylMassFamily.EquivariantFamily.sum,
  GUT.WeylMassFamily.EquivariantFamily.sum.eq_1 => Physics.WeylMassFamily.EquivariantFamily.sum.eq_1,
  GUT.WeylMassFamily.EquivariantFamily.sum_apply => Physics.WeylMassFamily.EquivariantFamily.sum_apply,
  GUT.WeylMassFamily.EquivariantFamily.sum_zero => Physics.WeylMassFamily.EquivariantFamily.sum_zero,
  GUT.WeylMassFamily.MultilinearCoupling => Physics.WeylMassFamily.MultilinearCoupling,
  GUT.WeylMassFamily.MultilinearCoupling.casesOn => Physics.WeylMassFamily.MultilinearCoupling.casesOn,
  GUT.WeylMassFamily.MultilinearCoupling.coefficient => Physics.WeylMassFamily.MultilinearCoupling.coefficient,
  GUT.WeylMassFamily.MultilinearCoupling.conjugateSlot => Physics.WeylMassFamily.MultilinearCoupling.conjugateSlot,
  GUT.WeylMassFamily.MultilinearCoupling.conjugateSlot_apply => Physics.WeylMassFamily.MultilinearCoupling.conjugateSlot_apply,
  GUT.WeylMassFamily.MultilinearCoupling.constant => Physics.WeylMassFamily.MultilinearCoupling.constant,
  GUT.WeylMassFamily.MultilinearCoupling.constant_toFamily => Physics.WeylMassFamily.MultilinearCoupling.constant_toFamily,
  GUT.WeylMassFamily.MultilinearCoupling.ctorIdx => Physics.WeylMassFamily.MultilinearCoupling.ctorIdx,
  GUT.WeylMassFamily.MultilinearCoupling.invariant => Physics.WeylMassFamily.MultilinearCoupling.invariant,
  GUT.WeylMassFamily.MultilinearCoupling.linearSlot => Physics.WeylMassFamily.MultilinearCoupling.linearSlot,
  GUT.WeylMassFamily.MultilinearCoupling.mk => Physics.WeylMassFamily.MultilinearCoupling.mk,
  GUT.WeylMassFamily.MultilinearCoupling.mk.inj => Physics.WeylMassFamily.MultilinearCoupling.mk.inj,
  GUT.WeylMassFamily.MultilinearCoupling.mk.injEq => Physics.WeylMassFamily.MultilinearCoupling.mk.injEq,
  GUT.WeylMassFamily.MultilinearCoupling.mk.noConfusion => Physics.WeylMassFamily.MultilinearCoupling.mk.noConfusion,
  GUT.WeylMassFamily.MultilinearCoupling.mk.sizeOf_spec => Physics.WeylMassFamily.MultilinearCoupling.mk.sizeOf_spec,
  GUT.WeylMassFamily.MultilinearCoupling.noConfusion => Physics.WeylMassFamily.MultilinearCoupling.noConfusion,
  GUT.WeylMassFamily.MultilinearCoupling.noConfusionType => Physics.WeylMassFamily.MultilinearCoupling.noConfusionType,
  GUT.WeylMassFamily.MultilinearCoupling.ofLinear => Physics.WeylMassFamily.MultilinearCoupling.ofLinear,
  GUT.WeylMassFamily.MultilinearCoupling.ofLinear_toFamily => Physics.WeylMassFamily.MultilinearCoupling.ofLinear_toFamily,
  GUT.WeylMassFamily.MultilinearCoupling.realCoefficient => Physics.WeylMassFamily.MultilinearCoupling.realCoefficient,
  GUT.WeylMassFamily.MultilinearCoupling.realCoefficient.congr_simp => Physics.WeylMassFamily.MultilinearCoupling.realCoefficient.congr_simp,
  GUT.WeylMassFamily.MultilinearCoupling.rec => Physics.WeylMassFamily.MultilinearCoupling.rec,
  GUT.WeylMassFamily.MultilinearCoupling.recOn => Physics.WeylMassFamily.MultilinearCoupling.recOn,
  GUT.WeylMassFamily.MultilinearCoupling.symmetric => Physics.WeylMassFamily.MultilinearCoupling.symmetric,
  GUT.WeylMassFamily.MultilinearCoupling.toFamily => Physics.WeylMassFamily.MultilinearCoupling.toFamily,
  GUT.WeylMassFamily.MultilinearCoupling.toFamily_apply => Physics.WeylMassFamily.MultilinearCoupling.toFamily_apply,
  GUT.WeylMassFamily.MultilinearCoupling.toFamily_realDiagonal => Physics.WeylMassFamily.MultilinearCoupling.toFamily_realDiagonal,
  GUT.WeylMassFamily.MultilinearCoupling.toFamily_real_homogeneous => Physics.WeylMassFamily.MultilinearCoupling.toFamily_real_homogeneous,
  GUT.WeylMassFamily.MultilinearCoupling.toFamily_zero => Physics.WeylMassFamily.MultilinearCoupling.toFamily_zero
]

assert_compatible GUT.WeylMassFamily.EquivariantFamily.mk.congr_simp => Physics.WeylMassFamily.EquivariantFamily.mk.congr_simp
assert_compatible GUT.WeylMassFamily.EquivariantFamily.sum => Physics.WeylMassFamily.EquivariantFamily.sum
assert_compatible GUT.WeylMassFamily.EquivariantFamily.sum.eq_1 => Physics.WeylMassFamily.EquivariantFamily.sum.eq_1
assert_compatible GUT.WeylMassFamily.EquivariantFamily.sum_apply => Physics.WeylMassFamily.EquivariantFamily.sum_apply
assert_compatible GUT.WeylMassFamily.EquivariantFamily.sum_zero => Physics.WeylMassFamily.EquivariantFamily.sum_zero
assert_compatible GUT.WeylMassFamily.MultilinearCoupling => Physics.WeylMassFamily.MultilinearCoupling
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.casesOn => Physics.WeylMassFamily.MultilinearCoupling.casesOn
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.coefficient => Physics.WeylMassFamily.MultilinearCoupling.coefficient
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.conjugateSlot => Physics.WeylMassFamily.MultilinearCoupling.conjugateSlot
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.conjugateSlot_apply => Physics.WeylMassFamily.MultilinearCoupling.conjugateSlot_apply
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.constant => Physics.WeylMassFamily.MultilinearCoupling.constant
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.constant_toFamily => Physics.WeylMassFamily.MultilinearCoupling.constant_toFamily
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.ctorIdx => Physics.WeylMassFamily.MultilinearCoupling.ctorIdx
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.invariant => Physics.WeylMassFamily.MultilinearCoupling.invariant
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.linearSlot => Physics.WeylMassFamily.MultilinearCoupling.linearSlot
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.mk => Physics.WeylMassFamily.MultilinearCoupling.mk
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.mk.inj => Physics.WeylMassFamily.MultilinearCoupling.mk.inj
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.mk.injEq => Physics.WeylMassFamily.MultilinearCoupling.mk.injEq
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.mk.noConfusion => Physics.WeylMassFamily.MultilinearCoupling.mk.noConfusion
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.mk.sizeOf_spec => Physics.WeylMassFamily.MultilinearCoupling.mk.sizeOf_spec
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.noConfusion => Physics.WeylMassFamily.MultilinearCoupling.noConfusion
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.noConfusionType => Physics.WeylMassFamily.MultilinearCoupling.noConfusionType
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.ofLinear => Physics.WeylMassFamily.MultilinearCoupling.ofLinear
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.ofLinear_toFamily => Physics.WeylMassFamily.MultilinearCoupling.ofLinear_toFamily
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.realCoefficient => Physics.WeylMassFamily.MultilinearCoupling.realCoefficient
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.realCoefficient.congr_simp => Physics.WeylMassFamily.MultilinearCoupling.realCoefficient.congr_simp
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.rec => Physics.WeylMassFamily.MultilinearCoupling.rec
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.recOn => Physics.WeylMassFamily.MultilinearCoupling.recOn
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.symmetric => Physics.WeylMassFamily.MultilinearCoupling.symmetric
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.toFamily => Physics.WeylMassFamily.MultilinearCoupling.toFamily
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.toFamily_apply => Physics.WeylMassFamily.MultilinearCoupling.toFamily_apply
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.toFamily_realDiagonal => Physics.WeylMassFamily.MultilinearCoupling.toFamily_realDiagonal
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.toFamily_real_homogeneous => Physics.WeylMassFamily.MultilinearCoupling.toFamily_real_homogeneous
assert_compatible GUT.WeylMassFamily.MultilinearCoupling.toFamily_zero => Physics.WeylMassFamily.MultilinearCoupling.toFamily_zero
