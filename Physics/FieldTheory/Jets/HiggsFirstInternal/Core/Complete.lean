import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero0
import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero1
import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero2
import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Zero3

/-! Two coordinates control every actual internally invariant quartic Higgs
first-jet functional. The caller need not assume hypercharge balance. -/
namespace Physics.HiggsFirstInternal
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls

theorem all_zero (f : A →ₗ[ℂ] ℂ)
    (hI : ∀ g i j k l, f (T g (mono i j k l)) = f (mono i j k l))
    (h0 : K f 0 0 2 2 = 0) (h2 : K f 2 0 0 2 = 0) (i j k l : Fin 4) :
    K f i j k l = 0 := by
  fin_cases i
  · exact zero0 f hI h0 h2 j k l
  · exact zero1 f hI h0 h2 j k l
  · exact zero2 f hI h0 h2 j k l
  · exact zero3 f hI h0 h2 j k l

end
end Physics.HiggsFirstInternal
