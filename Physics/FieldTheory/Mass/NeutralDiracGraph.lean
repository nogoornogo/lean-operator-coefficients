import Physics.FieldTheory.Mass.Algebra.NeutralDiracGraph
import Physics.FieldTheory.Mass.DiracWeylConvention
import Math.LinearAlgebra.NeutralKernelGraph
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Mass.Algebra.NeutralDiracGraph instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.NeutralDiracGraph.kernel_iff => Physics.NeutralDiracGraph.kernel_iff,
  GUT.NeutralDiracGraph.light => Physics.NeutralDiracGraph.light,
  GUT.NeutralDiracGraph.light_coordinates => Physics.NeutralDiracGraph.light_coordinates,
  GUT.NeutralDiracGraph.light_mem => Physics.NeutralDiracGraph.light_mem,
  GUT.NeutralDiracGraph.mass_symmetric => Physics.NeutralDiracGraph.mass_symmetric,
  GUT.NeutralDiracGraph.mixingMap => Physics.NeutralDiracGraph.mixingMap,
  GUT.NeutralDiracGraph.mixingMap.eq_1 => Physics.NeutralDiracGraph.mixingMap.eq_1,
  GUT.NeutralDiracGraph.restrict => Physics.NeutralDiracGraph.restrict,
  GUT.NeutralDiracGraph.restrict_zero_iff => Physics.NeutralDiracGraph.restrict_zero_iff
]

assert_compatible GUT.NeutralDiracGraph.kernel_iff => Physics.NeutralDiracGraph.kernel_iff
assert_compatible GUT.NeutralDiracGraph.light => Physics.NeutralDiracGraph.light
assert_compatible GUT.NeutralDiracGraph.light_coordinates => Physics.NeutralDiracGraph.light_coordinates
assert_compatible GUT.NeutralDiracGraph.light_mem => Physics.NeutralDiracGraph.light_mem
assert_compatible GUT.NeutralDiracGraph.mass_symmetric => Physics.NeutralDiracGraph.mass_symmetric
assert_compatible GUT.NeutralDiracGraph.mixingMap => Physics.NeutralDiracGraph.mixingMap
assert_compatible GUT.NeutralDiracGraph.mixingMap.eq_1 => Physics.NeutralDiracGraph.mixingMap.eq_1
assert_compatible GUT.NeutralDiracGraph.restrict => Physics.NeutralDiracGraph.restrict
assert_compatible GUT.NeutralDiracGraph.restrict_zero_iff => Physics.NeutralDiracGraph.restrict_zero_iff
