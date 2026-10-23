import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero3
import Physics.FieldTheory.Jets.HiggsFirstInternal.Rows
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero3 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.zero3 => Physics.HiggsFirstInternal.zero3
]

assert_compatible GUT.HiggsFirstInternal.zero3 => Physics.HiggsFirstInternal.zero3
