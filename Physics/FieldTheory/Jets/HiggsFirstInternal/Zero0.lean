import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero0
import Physics.FieldTheory.Jets.HiggsFirstInternal.Rows
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero0 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.zero0 => Physics.HiggsFirstInternal.zero0
]

assert_compatible GUT.HiggsFirstInternal.zero0 => Physics.HiggsFirstInternal.zero0
