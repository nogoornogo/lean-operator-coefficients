import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero2
import Physics.FieldTheory.Jets.HiggsFirstInternal.Rows
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero2 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.zero2 => Physics.HiggsFirstInternal.zero2
]

assert_compatible GUT.HiggsFirstInternal.zero2 => Physics.HiggsFirstInternal.zero2
