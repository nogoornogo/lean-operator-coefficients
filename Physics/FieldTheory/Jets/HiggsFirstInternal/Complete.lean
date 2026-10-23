import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Complete
import Physics.FieldTheory.Jets.HiggsFirstInternal.Zero0
import Physics.FieldTheory.Jets.HiggsFirstInternal.Zero1
import Physics.FieldTheory.Jets.HiggsFirstInternal.Zero2
import Physics.FieldTheory.Jets.HiggsFirstInternal.Zero3
import Math.Lean.Compatibility

deprecated_module "Use Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Complete instead." (since := "source-api-v1")

compatibility_declarations [
  GUT.HiggsFirstInternal.all_zero => Physics.HiggsFirstInternal.all_zero
]

assert_compatible GUT.HiggsFirstInternal.all_zero => Physics.HiggsFirstInternal.all_zero
