import Physics.FieldTheory.Spinor.Weyl.WeylGeneratorTests
import Physics.FieldTheory.Spinor.WeylSpinor
import Math.RepresentationTheory.GeneratorInvariantTests
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Spinor.Weyl.WeylGeneratorTests instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.WeylGeneratorTests.Index => Physics.WeylGeneratorTests.Index,
  GUT.WeylGeneratorTests.generates => Physics.WeylGeneratorTests.generates,
  GUT.WeylGeneratorTests.generator => Physics.WeylGeneratorTests.generator,
  GUT.WeylGeneratorTests.invariant_iff => Physics.WeylGeneratorTests.invariant_iff
]

assert_compatible GUT.WeylGeneratorTests.Index => Physics.WeylGeneratorTests.Index
assert_compatible GUT.WeylGeneratorTests.generates => Physics.WeylGeneratorTests.generates
assert_compatible GUT.WeylGeneratorTests.generator => Physics.WeylGeneratorTests.generator
assert_compatible GUT.WeylGeneratorTests.invariant_iff => Physics.WeylGeneratorTests.invariant_iff
