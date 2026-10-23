import Physics.FieldTheory.Jets.Gauge.YangMillsControls
import Physics.FieldTheory.Jets.FormalYangMills
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.YangMillsControls instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FormalYangMills.Controls.N => Physics.FormalYangMills.Controls.N,
  GUT.FormalYangMills.Controls.curvature_evaluation => Physics.FormalYangMills.Controls.curvature_evaluation,
  GUT.FormalYangMills.Controls.equation_evaluation => Physics.FormalYangMills.Controls.equation_evaluation,
  GUT.FormalYangMills.Controls.evaluation => Physics.FormalYangMills.Controls.evaluation,
  GUT.FormalYangMills.Controls.evaluation_F => Physics.FormalYangMills.Controls.evaluation_F,
  GUT.FormalYangMills.Controls.evaluation_connection => Physics.FormalYangMills.Controls.evaluation_connection,
  GUT.FormalYangMills.Controls.evaluation_derivative => Physics.FormalYangMills.Controls.evaluation_derivative,
  GUT.FormalYangMills.Controls.evaluation_nabla => Physics.FormalYangMills.Controls.evaluation_nabla,
  GUT.FormalYangMills.Controls.matrixEvaluation => Physics.FormalYangMills.Controls.matrixEvaluation,
  GUT.FormalYangMills.Controls.offShell_equation_nonzero => Physics.FormalYangMills.Controls.offShell_equation_nonzero,
  GUT.FormalYangMills.Controls.onShell_equation_zero => Physics.FormalYangMills.Controls.onShell_equation_zero,
  GUT.FormalYangMills.Controls.values => Physics.FormalYangMills.Controls.values,
  GUT.FormalYangMills.Controls.values.eq_1 => Physics.FormalYangMills.Controls.values.eq_1,
  GUT.FormalYangMills.sign.eq_1 => Physics.FormalYangMills.sign.eq_1
]

assert_compatible GUT.FormalYangMills.Controls.N => Physics.FormalYangMills.Controls.N
assert_compatible GUT.FormalYangMills.Controls.curvature_evaluation => Physics.FormalYangMills.Controls.curvature_evaluation
assert_compatible GUT.FormalYangMills.Controls.equation_evaluation => Physics.FormalYangMills.Controls.equation_evaluation
assert_compatible GUT.FormalYangMills.Controls.evaluation => Physics.FormalYangMills.Controls.evaluation
assert_compatible GUT.FormalYangMills.Controls.evaluation_F => Physics.FormalYangMills.Controls.evaluation_F
assert_compatible GUT.FormalYangMills.Controls.evaluation_connection => Physics.FormalYangMills.Controls.evaluation_connection
assert_compatible GUT.FormalYangMills.Controls.evaluation_derivative => Physics.FormalYangMills.Controls.evaluation_derivative
assert_compatible GUT.FormalYangMills.Controls.evaluation_nabla => Physics.FormalYangMills.Controls.evaluation_nabla
assert_compatible GUT.FormalYangMills.Controls.matrixEvaluation => Physics.FormalYangMills.Controls.matrixEvaluation
assert_compatible GUT.FormalYangMills.Controls.offShell_equation_nonzero => Physics.FormalYangMills.Controls.offShell_equation_nonzero
assert_compatible GUT.FormalYangMills.Controls.onShell_equation_zero => Physics.FormalYangMills.Controls.onShell_equation_zero
assert_compatible GUT.FormalYangMills.Controls.values => Physics.FormalYangMills.Controls.values
assert_compatible GUT.FormalYangMills.Controls.values.eq_1 => Physics.FormalYangMills.Controls.values.eq_1
assert_compatible GUT.FormalYangMills.sign.eq_1 => Physics.FormalYangMills.sign.eq_1
