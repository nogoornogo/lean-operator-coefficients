import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero1
import Physics.FieldTheory.Jets.HiggsFirstInternal.Rows
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero1 instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.zero1 => Physics.HiggsFirstInternal.zero1
]

assert_compatible GUT.HiggsFirstInternal.zero1 => Physics.HiggsFirstInternal.zero1
