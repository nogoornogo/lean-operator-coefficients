import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlExchange
import Physics.StandardModel.Gauge.SMEpsilonTensor
import Math.LinearAlgebra.StatisticalCompleteness
import Math.Lean.Compatibility

deprecated_module "Use Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlExchange instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.QqqlExchange.Antisymmetric => Physics.QqqlExchange.Antisymmetric,
  GUT.QqqlExchange.Condition => Physics.QqqlExchange.Condition,
  GUT.QqqlExchange.Family => Physics.QqqlExchange.Family,
  GUT.QqqlExchange.Residual => Physics.QqqlExchange.Residual,
  GUT.QqqlExchange.antisymmetric_iff => Physics.QqqlExchange.antisymmetric_iff,
  GUT.QqqlExchange.contraction => Physics.QqqlExchange.contraction,
  GUT.QqqlExchange.contraction.eq_1 => Physics.QqqlExchange.contraction.eq_1,
  GUT.QqqlExchange.local_statistics_iff => Physics.QqqlExchange.local_statistics_iff,
  GUT.QqqlExchange.reconstructLinear => Physics.QqqlExchange.reconstructLinear,
  GUT.QqqlExchange.reconstructLinear.eq_1 => Physics.QqqlExchange.reconstructLinear.eq_1,
  GUT.QqqlExchange.reconstruct_injective => Physics.QqqlExchange.reconstruct_injective,
  GUT.QqqlExchange.residualSpace => Physics.QqqlExchange.residualSpace,
  GUT.QqqlExchange.swap01 => Physics.QqqlExchange.swap01,
  GUT.QqqlExchange.swap12 => Physics.QqqlExchange.swap12,
  GUT.QqqlExchange.values => Physics.QqqlExchange.values,
  GUT.QqqlExchange.values.eq_1 => Physics.QqqlExchange.values.eq_1
]

assert_compatible GUT.QqqlExchange.Antisymmetric => Physics.QqqlExchange.Antisymmetric
assert_compatible GUT.QqqlExchange.Condition => Physics.QqqlExchange.Condition
assert_compatible GUT.QqqlExchange.Family => Physics.QqqlExchange.Family
assert_compatible GUT.QqqlExchange.Residual => Physics.QqqlExchange.Residual
assert_compatible GUT.QqqlExchange.antisymmetric_iff => Physics.QqqlExchange.antisymmetric_iff
assert_compatible GUT.QqqlExchange.contraction => Physics.QqqlExchange.contraction
assert_compatible GUT.QqqlExchange.contraction.eq_1 => Physics.QqqlExchange.contraction.eq_1
assert_compatible GUT.QqqlExchange.local_statistics_iff => Physics.QqqlExchange.local_statistics_iff
assert_compatible GUT.QqqlExchange.reconstructLinear => Physics.QqqlExchange.reconstructLinear
assert_compatible GUT.QqqlExchange.reconstructLinear.eq_1 => Physics.QqqlExchange.reconstructLinear.eq_1
assert_compatible GUT.QqqlExchange.reconstruct_injective => Physics.QqqlExchange.reconstruct_injective
assert_compatible GUT.QqqlExchange.residualSpace => Physics.QqqlExchange.residualSpace
assert_compatible GUT.QqqlExchange.swap01 => Physics.QqqlExchange.swap01
assert_compatible GUT.QqqlExchange.swap12 => Physics.QqqlExchange.swap12
assert_compatible GUT.QqqlExchange.values => Physics.QqqlExchange.values
assert_compatible GUT.QqqlExchange.values.eq_1 => Physics.QqqlExchange.values.eq_1
