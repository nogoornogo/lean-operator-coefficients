import Physics.FieldTheory.Jets.HiggsFirstInternal.Core.Rows

/-! Generated sparse certificates; Lean checks every actual-group identity. -/
namespace Physics.HiggsFirstInternal
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs HiggsQuarticFourInternalControls
attribute [local simp] mul_add add_mul sub_mul mul_sub smul_mul_assoc mul_smul_comm smul_smul smul_eq_mul
variable (f : A →ₗ[ℂ] ℂ)
  (hI : ∀ g i j k l, f (T g (mono i j k l)) = f (mono i j k l))


include hI in
theorem zero1 (h0 : K f 0 0 2 2 = 0) (_h2 : K f 2 0 0 2 = 0)
    (j k l : Fin 4) : K f 1 j k l = 0 := by
  fin_cases j <;> fin_cases k <;> fin_cases l
  · exact vanish f hI 1 0 0 0 (by decide +kernel)
  · exact vanish f hI 1 0 0 1 (by decide +kernel)
  · exact vanish f hI 1 0 0 2 (by decide +kernel)
  · exact vanish f hI 1 0 0 3 (by decide +kernel)
  · exact vanish f hI 1 0 1 0 (by decide +kernel)
  · exact vanish f hI 1 0 1 1 (by decide +kernel)
  · exact vanish f hI 1 0 1 2 (by decide +kernel)
  · exact vanish f hI 1 0 1 3 (by decide +kernel)
  · exact vanish f hI 1 0 2 0 (by decide +kernel)
  · exact vanish f hI 1 0 2 1 (by decide +kernel)
  · exact vanish f hI 1 0 2 2 (by decide +kernel)
  · change K f 1 0 2 3 = 0
    rw [normalize f 1 0 2 3]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 0 3 0 (by decide +kernel)
  · exact vanish f hI 1 0 3 1 (by decide +kernel)
  · change K f 1 0 3 2 = 0
    rw [normalize f 1 0 3 2]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 0 3 3 (by decide +kernel)
  · exact vanish f hI 1 1 0 0 (by decide +kernel)
  · exact vanish f hI 1 1 0 1 (by decide +kernel)
  · exact vanish f hI 1 1 0 2 (by decide +kernel)
  · exact vanish f hI 1 1 0 3 (by decide +kernel)
  · exact vanish f hI 1 1 1 0 (by decide +kernel)
  · exact vanish f hI 1 1 1 1 (by decide +kernel)
  · exact vanish f hI 1 1 1 2 (by decide +kernel)
  · exact vanish f hI 1 1 1 3 (by decide +kernel)
  · exact vanish f hI 1 1 2 0 (by decide +kernel)
  · exact vanish f hI 1 1 2 1 (by decide +kernel)
  · exact vanish f hI 1 1 2 2 (by decide +kernel)
  · exact vanish f hI 1 1 2 3 (by decide +kernel)
  · exact vanish f hI 1 1 3 0 (by decide +kernel)
  · exact vanish f hI 1 1 3 1 (by decide +kernel)
  · exact vanish f hI 1 1 3 2 (by decide +kernel)
  · change K f 1 1 3 3 = 0
    rw [normalize f 1 1 3 3]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 2 0 0 (by decide +kernel)
  · exact vanish f hI 1 2 0 1 (by decide +kernel)
  · exact vanish f hI 1 2 0 2 (by decide +kernel)
  · change K f 1 2 0 3 = 0
    rw [normalize f 1 2 0 3]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 2 1 0 (by decide +kernel)
  · exact vanish f hI 1 2 1 1 (by decide +kernel)
  · exact vanish f hI 1 2 1 2 (by decide +kernel)
  · exact vanish f hI 1 2 1 3 (by decide +kernel)
  · exact vanish f hI 1 2 2 0 (by decide +kernel)
  · exact vanish f hI 1 2 2 1 (by decide +kernel)
  · exact vanish f hI 1 2 2 2 (by decide +kernel)
  · exact vanish f hI 1 2 2 3 (by decide +kernel)
  · change K f 1 2 3 0 = 0
    rw [normalize f 1 2 3 0]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 2 3 1 (by decide +kernel)
  · exact vanish f hI 1 2 3 2 (by decide +kernel)
  · exact vanish f hI 1 2 3 3 (by decide +kernel)
  · exact vanish f hI 1 3 0 0 (by decide +kernel)
  · exact vanish f hI 1 3 0 1 (by decide +kernel)
  · change K f 1 3 0 2 = 0
    rw [normalize f 1 3 0 2]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 3 0 3 (by decide +kernel)
  · exact vanish f hI 1 3 1 0 (by decide +kernel)
  · exact vanish f hI 1 3 1 1 (by decide +kernel)
  · exact vanish f hI 1 3 1 2 (by decide +kernel)
  · change K f 1 3 1 3 = 0
    rw [normalize f 1 3 1 3]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · change K f 1 3 2 0 = 0
    rw [normalize f 1 3 2 0]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 3 2 1 (by decide +kernel)
  · exact vanish f hI 1 3 2 2 (by decide +kernel)
  · exact vanish f hI 1 3 2 3 (by decide +kernel)
  · exact vanish f hI 1 3 3 0 (by decide +kernel)
  · change K f 1 3 3 1 = 0
    rw [normalize f 1 3 3 1]
    norm_num [ordered,value3113 f hI,value3012 f hI,value2013 f hI,value1133 f hI,value1023 f hI,value0123 f hI,h0,_h2]
  · exact vanish f hI 1 3 3 2 (by decide +kernel)
  · exact vanish f hI 1 3 3 3 (by decide +kernel)

end
end Physics.HiggsFirstInternal
