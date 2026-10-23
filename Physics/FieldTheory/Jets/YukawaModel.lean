import Physics.FieldTheory.Jets.Lagrangian.YukawaModel
import Math.Algebra.ScalarWeylYukawa
import Math.Algebra.MixedScalarInclusion
import Math.RepresentationTheory.LagrangianModel
import Physics.FieldTheory.Jets.PairedWeylGeneratedInput
import Physics.FieldTheory.Jets.HiggsLagrangianInput
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Lagrangian.YukawaModel instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.YukawaModel.Equations => Physics.YukawaModel.Equations,
  GUT.YukawaModel.Group => Physics.YukawaModel.Group,
  GUT.YukawaModel.Spinor => Physics.YukawaModel.Spinor,
  GUT.YukawaModel.action_mul => Physics.YukawaModel.action_mul,
  GUT.YukawaModel.coefficient_roundtrip => Physics.YukawaModel.coefficient_roundtrip,
  GUT.YukawaModel.equationMap => Physics.YukawaModel.equationMap,
  GUT.YukawaModel.equationMap.eq_1 => Physics.YukawaModel.equationMap.eq_1,
  GUT.YukawaModel.equationMap_covariant => Physics.YukawaModel.equationMap_covariant,
  GUT.YukawaModel.equationMap_row => Physics.YukawaModel.equationMap_row,
  GUT.YukawaModel.euler_equals_independent => Physics.YukawaModel.euler_equals_independent,
  GUT.YukawaModel.euler_span_stable => Physics.YukawaModel.euler_span_stable,
  GUT.YukawaModel.evenEquation_invariant => Physics.YukawaModel.evenEquation_invariant,
  GUT.YukawaModel.even_transport => Physics.YukawaModel.even_transport,
  GUT.YukawaModel.full_relations => Physics.YukawaModel.full_relations,
  GUT.YukawaModel.independentEuler => Physics.YukawaModel.independentEuler,
  GUT.YukawaModel.input => Physics.YukawaModel.input,
  GUT.YukawaModel.instAddCommGroupA_physics => Physics.YukawaModel.instAddCommGroupA_physics,
  GUT.YukawaModel.instModuleComplexA_physics => Physics.YukawaModel.instModuleComplexA_physics,
  GUT.YukawaModel.instRingA_physics => Physics.YukawaModel.instRingA_physics,
  GUT.YukawaModel.kineticMap => Physics.YukawaModel.kineticMap,
  GUT.YukawaModel.kineticMap.eq_1 => Physics.YukawaModel.kineticMap.eq_1,
  GUT.YukawaModel.kineticMap_covariant => Physics.YukawaModel.kineticMap_covariant,
  GUT.YukawaModel.massMap => Physics.YukawaModel.massMap,
  GUT.YukawaModel.massMap_covariant => Physics.YukawaModel.massMap_covariant,
  GUT.YukawaModel.model => Physics.YukawaModel.model,
  GUT.YukawaModel.odd_coefficient_equation => Physics.YukawaModel.odd_coefficient_equation,
  GUT.YukawaModel.pair_invariant => Physics.YukawaModel.pair_invariant,
  GUT.YukawaModel.phi_invariant => Physics.YukawaModel.phi_invariant,
  GUT.YukawaModel.raise => Physics.YukawaModel.raise,
  GUT.YukawaModel.raise.eq_1 => Physics.YukawaModel.raise.eq_1,
  GUT.YukawaModel.raise_covariant => Physics.YukawaModel.raise_covariant,
  GUT.YukawaModel.raise_pair => Physics.YukawaModel.raise_pair,
  GUT.YukawaModel.raise_row => Physics.YukawaModel.raise_row,
  GUT.YukawaModel.scalar_coefficient_equation => Physics.YukawaModel.scalar_coefficient_equation,
  GUT.YukawaModel.spin => Physics.YukawaModel.spin,
  GUT.YukawaModel.spin_pair => Physics.YukawaModel.spin_pair,
  GUT.YukawaModel.wave_invariant => Physics.YukawaModel.wave_invariant,
  GUT.YukawaModel.zeroOdd => Physics.YukawaModel.zeroOdd,
  GUT.YukawaModel.zeroOdd.eq_1 => Physics.YukawaModel.zeroOdd.eq_1,
  GUT.YukawaModel.zeroOdd_basis => Physics.YukawaModel.zeroOdd_basis,
  GUT.YukawaModel.zeroOdd_covariant => Physics.YukawaModel.zeroOdd_covariant,
  GUT.YukawaModel.zeroOdd_expand => Physics.YukawaModel.zeroOdd_expand,
  GUT.YukawaModel.zeroOdd_product => Physics.YukawaModel.zeroOdd_product
]

assert_compatible GUT.YukawaModel.Equations => Physics.YukawaModel.Equations
assert_compatible GUT.YukawaModel.Group => Physics.YukawaModel.Group
assert_compatible GUT.YukawaModel.Spinor => Physics.YukawaModel.Spinor
assert_compatible GUT.YukawaModel.action_mul => Physics.YukawaModel.action_mul
assert_compatible GUT.YukawaModel.coefficient_roundtrip => Physics.YukawaModel.coefficient_roundtrip
assert_compatible GUT.YukawaModel.equationMap => Physics.YukawaModel.equationMap
assert_compatible GUT.YukawaModel.equationMap.eq_1 => Physics.YukawaModel.equationMap.eq_1
assert_compatible GUT.YukawaModel.equationMap_covariant => Physics.YukawaModel.equationMap_covariant
assert_compatible GUT.YukawaModel.equationMap_row => Physics.YukawaModel.equationMap_row
assert_compatible GUT.YukawaModel.euler_equals_independent => Physics.YukawaModel.euler_equals_independent
assert_compatible GUT.YukawaModel.euler_span_stable => Physics.YukawaModel.euler_span_stable
assert_compatible GUT.YukawaModel.evenEquation_invariant => Physics.YukawaModel.evenEquation_invariant
assert_compatible GUT.YukawaModel.even_transport => Physics.YukawaModel.even_transport
assert_compatible GUT.YukawaModel.full_relations => Physics.YukawaModel.full_relations
assert_compatible GUT.YukawaModel.independentEuler => Physics.YukawaModel.independentEuler
assert_compatible GUT.YukawaModel.input => Physics.YukawaModel.input
assert_compatible GUT.YukawaModel.instAddCommGroupA_physics => Physics.YukawaModel.instAddCommGroupA_physics
assert_compatible GUT.YukawaModel.instModuleComplexA_physics => Physics.YukawaModel.instModuleComplexA_physics
assert_compatible GUT.YukawaModel.instRingA_physics => Physics.YukawaModel.instRingA_physics
assert_compatible GUT.YukawaModel.kineticMap => Physics.YukawaModel.kineticMap
assert_compatible GUT.YukawaModel.kineticMap.eq_1 => Physics.YukawaModel.kineticMap.eq_1
assert_compatible GUT.YukawaModel.kineticMap_covariant => Physics.YukawaModel.kineticMap_covariant
assert_compatible GUT.YukawaModel.massMap => Physics.YukawaModel.massMap
assert_compatible GUT.YukawaModel.massMap_covariant => Physics.YukawaModel.massMap_covariant
assert_compatible GUT.YukawaModel.model => Physics.YukawaModel.model
assert_compatible GUT.YukawaModel.odd_coefficient_equation => Physics.YukawaModel.odd_coefficient_equation
assert_compatible GUT.YukawaModel.pair_invariant => Physics.YukawaModel.pair_invariant
assert_compatible GUT.YukawaModel.phi_invariant => Physics.YukawaModel.phi_invariant
assert_compatible GUT.YukawaModel.raise => Physics.YukawaModel.raise
assert_compatible GUT.YukawaModel.raise.eq_1 => Physics.YukawaModel.raise.eq_1
assert_compatible GUT.YukawaModel.raise_covariant => Physics.YukawaModel.raise_covariant
assert_compatible GUT.YukawaModel.raise_pair => Physics.YukawaModel.raise_pair
assert_compatible GUT.YukawaModel.raise_row => Physics.YukawaModel.raise_row
assert_compatible GUT.YukawaModel.scalar_coefficient_equation => Physics.YukawaModel.scalar_coefficient_equation
assert_compatible GUT.YukawaModel.spin => Physics.YukawaModel.spin
assert_compatible GUT.YukawaModel.spin_pair => Physics.YukawaModel.spin_pair
assert_compatible GUT.YukawaModel.wave_invariant => Physics.YukawaModel.wave_invariant
assert_compatible GUT.YukawaModel.zeroOdd => Physics.YukawaModel.zeroOdd
assert_compatible GUT.YukawaModel.zeroOdd.eq_1 => Physics.YukawaModel.zeroOdd.eq_1
assert_compatible GUT.YukawaModel.zeroOdd_basis => Physics.YukawaModel.zeroOdd_basis
assert_compatible GUT.YukawaModel.zeroOdd_covariant => Physics.YukawaModel.zeroOdd_covariant
assert_compatible GUT.YukawaModel.zeroOdd_expand => Physics.YukawaModel.zeroOdd_expand
assert_compatible GUT.YukawaModel.zeroOdd_product => Physics.YukawaModel.zeroOdd_product
