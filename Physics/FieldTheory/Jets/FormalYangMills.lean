import Physics.FieldTheory.Jets.Gauge.FormalYangMills
import Math.Algebra.MatrixJetConnection
import Math.RepresentationTheory.NonlinearJetIBP
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.Gauge.FormalYangMills instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.FormalYangMills.Components => Physics.FormalYangMills.Components,
  GUT.FormalYangMills.D => Physics.FormalYangMills.D,
  GUT.FormalYangMills.F => Physics.FormalYangMills.F,
  GUT.FormalYangMills.Mat => Physics.FormalYangMills.Mat,
  GUT.FormalYangMills.OffShell => Physics.FormalYangMills.OffShell,
  GUT.FormalYangMills.Shell => Physics.FormalYangMills.Shell,
  GUT.FormalYangMills.bianchi => Physics.FormalYangMills.bianchi,
  GUT.FormalYangMills.coefficientEquiv => Physics.FormalYangMills.coefficientEquiv,
  GUT.FormalYangMills.commutator => Physics.FormalYangMills.commutator,
  GUT.FormalYangMills.connection => Physics.FormalYangMills.connection,
  GUT.FormalYangMills.covariantWord => Physics.FormalYangMills.covariantWord,
  GUT.FormalYangMills.covariant_descendants_mem => Physics.FormalYangMills.covariant_descendants_mem,
  GUT.FormalYangMills.covariant_descendants_zero => Physics.FormalYangMills.covariant_descendants_zero,
  GUT.FormalYangMills.curvature_antisymmetric => Physics.FormalYangMills.curvature_antisymmetric,
  GUT.FormalYangMills.descendants_zero => Physics.FormalYangMills.descendants_zero,
  GUT.FormalYangMills.entriesMem => Physics.FormalYangMills.entriesMem,
  GUT.FormalYangMills.entries_mul_left => Physics.FormalYangMills.entries_mul_left,
  GUT.FormalYangMills.entries_mul_right => Physics.FormalYangMills.entries_mul_right,
  GUT.FormalYangMills.entries_nabla => Physics.FormalYangMills.entries_nabla,
  GUT.FormalYangMills.equation => Physics.FormalYangMills.equation,
  GUT.FormalYangMills.equation.eq_1 => Physics.FormalYangMills.equation.eq_1,
  GUT.FormalYangMills.equation_mem => Physics.FormalYangMills.equation_mem,
  GUT.FormalYangMills.equations => Physics.FormalYangMills.equations,
  GUT.FormalYangMills.finiteImage => Physics.FormalYangMills.finiteImage,
  GUT.FormalYangMills.finiteImage_finite => Physics.FormalYangMills.finiteImage_finite,
  GUT.FormalYangMills.ideal => Physics.FormalYangMills.ideal,
  GUT.FormalYangMills.nabla => Physics.FormalYangMills.nabla,
  GUT.FormalYangMills.ordinary => Physics.FormalYangMills.ordinary,
  GUT.FormalYangMills.projection => Physics.FormalYangMills.projection,
  GUT.FormalYangMills.projection_kernel => Physics.FormalYangMills.projection_kernel,
  GUT.FormalYangMills.projection_surjective => Physics.FormalYangMills.projection_surjective,
  GUT.FormalYangMills.sign => Physics.FormalYangMills.sign,
  GUT.FormalYangMills.sourceEquiv => Physics.FormalYangMills.sourceEquiv,
  GUT.FormalYangMills.unit_survives => Physics.FormalYangMills.unit_survives,
  GUT.FormalYangMills.zeroEvaluation_F => Physics.FormalYangMills.zeroEvaluation_F,
  GUT.FormalYangMills.zeroEvaluation_connection => Physics.FormalYangMills.zeroEvaluation_connection,
  GUT.FormalYangMills.zeroEvaluation_equation => Physics.FormalYangMills.zeroEvaluation_equation
]

assert_compatible GUT.FormalYangMills.Components => Physics.FormalYangMills.Components
assert_compatible GUT.FormalYangMills.D => Physics.FormalYangMills.D
assert_compatible GUT.FormalYangMills.F => Physics.FormalYangMills.F
assert_compatible GUT.FormalYangMills.Mat => Physics.FormalYangMills.Mat
assert_compatible GUT.FormalYangMills.OffShell => Physics.FormalYangMills.OffShell
assert_compatible GUT.FormalYangMills.Shell => Physics.FormalYangMills.Shell
assert_compatible GUT.FormalYangMills.bianchi => Physics.FormalYangMills.bianchi
assert_compatible GUT.FormalYangMills.coefficientEquiv => Physics.FormalYangMills.coefficientEquiv
assert_compatible GUT.FormalYangMills.commutator => Physics.FormalYangMills.commutator
assert_compatible GUT.FormalYangMills.connection => Physics.FormalYangMills.connection
assert_compatible GUT.FormalYangMills.covariantWord => Physics.FormalYangMills.covariantWord
assert_compatible GUT.FormalYangMills.covariant_descendants_mem => Physics.FormalYangMills.covariant_descendants_mem
assert_compatible GUT.FormalYangMills.covariant_descendants_zero => Physics.FormalYangMills.covariant_descendants_zero
assert_compatible GUT.FormalYangMills.curvature_antisymmetric => Physics.FormalYangMills.curvature_antisymmetric
assert_compatible GUT.FormalYangMills.descendants_zero => Physics.FormalYangMills.descendants_zero
assert_compatible GUT.FormalYangMills.entriesMem => Physics.FormalYangMills.entriesMem
assert_compatible GUT.FormalYangMills.entries_mul_left => Physics.FormalYangMills.entries_mul_left
assert_compatible GUT.FormalYangMills.entries_mul_right => Physics.FormalYangMills.entries_mul_right
assert_compatible GUT.FormalYangMills.entries_nabla => Physics.FormalYangMills.entries_nabla
assert_compatible GUT.FormalYangMills.equation => Physics.FormalYangMills.equation
assert_compatible GUT.FormalYangMills.equation.eq_1 => Physics.FormalYangMills.equation.eq_1
assert_compatible GUT.FormalYangMills.equation_mem => Physics.FormalYangMills.equation_mem
assert_compatible GUT.FormalYangMills.equations => Physics.FormalYangMills.equations
assert_compatible GUT.FormalYangMills.finiteImage => Physics.FormalYangMills.finiteImage
assert_compatible GUT.FormalYangMills.finiteImage_finite => Physics.FormalYangMills.finiteImage_finite
assert_compatible GUT.FormalYangMills.ideal => Physics.FormalYangMills.ideal
assert_compatible GUT.FormalYangMills.nabla => Physics.FormalYangMills.nabla
assert_compatible GUT.FormalYangMills.ordinary => Physics.FormalYangMills.ordinary
assert_compatible GUT.FormalYangMills.projection => Physics.FormalYangMills.projection
assert_compatible GUT.FormalYangMills.projection_kernel => Physics.FormalYangMills.projection_kernel
assert_compatible GUT.FormalYangMills.projection_surjective => Physics.FormalYangMills.projection_surjective
assert_compatible GUT.FormalYangMills.sign => Physics.FormalYangMills.sign
assert_compatible GUT.FormalYangMills.sourceEquiv => Physics.FormalYangMills.sourceEquiv
assert_compatible GUT.FormalYangMills.unit_survives => Physics.FormalYangMills.unit_survives
assert_compatible GUT.FormalYangMills.zeroEvaluation_F => Physics.FormalYangMills.zeroEvaluation_F
assert_compatible GUT.FormalYangMills.zeroEvaluation_connection => Physics.FormalYangMills.zeroEvaluation_connection
assert_compatible GUT.FormalYangMills.zeroEvaluation_equation => Physics.FormalYangMills.zeroEvaluation_equation
