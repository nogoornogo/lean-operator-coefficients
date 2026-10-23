import Physics.FieldTheory.Jets.Gauge.YangMillsGaugeTrace
import Math.Algebra.FormalGaugeTransformation
import Math.Algebra.MatrixTraceIBP
import Physics.FieldTheory.Jets.FormalYangMills
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.YangMillsGaugeTrace instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FormalYangMills.local_curvature => Physics.FormalYangMills.local_curvature,
  GUT.FormalYangMills.local_equation => Physics.FormalYangMills.local_equation,
  GUT.FormalYangMills.local_equation_mem => Physics.FormalYangMills.local_equation_mem,
  GUT.FormalYangMills.local_equation_zero => Physics.FormalYangMills.local_equation_zero,
  GUT.FormalYangMills.trace_ibp => Physics.FormalYangMills.trace_ibp,
  GUT.FormalYangMills.trace_ibp_onShell => Physics.FormalYangMills.trace_ibp_onShell,
  GUT.FormalYangMills.trace_local_curvature_square => Physics.FormalYangMills.trace_local_curvature_square,
  GUT.FormalYangMills.transformedConnection => Physics.FormalYangMills.transformedConnection
]

assert_compatible GUT.FormalYangMills.local_curvature => Physics.FormalYangMills.local_curvature
assert_compatible GUT.FormalYangMills.local_equation => Physics.FormalYangMills.local_equation
assert_compatible GUT.FormalYangMills.local_equation_mem => Physics.FormalYangMills.local_equation_mem
assert_compatible GUT.FormalYangMills.local_equation_zero => Physics.FormalYangMills.local_equation_zero
assert_compatible GUT.FormalYangMills.trace_ibp => Physics.FormalYangMills.trace_ibp
assert_compatible GUT.FormalYangMills.trace_ibp_onShell => Physics.FormalYangMills.trace_ibp_onShell
assert_compatible GUT.FormalYangMills.trace_local_curvature_square => Physics.FormalYangMills.trace_local_curvature_square
assert_compatible GUT.FormalYangMills.transformedConnection => Physics.FormalYangMills.transformedConnection
