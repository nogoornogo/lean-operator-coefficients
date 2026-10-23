import Physics.FieldTheory.Jets.LorentzRankFour.Core.Components1

/-! Generated exact certificates; see generate-rank-four-control.py.
Each identity is rechecked by Lean, without imported rank premises. -/
namespace Physics.LorentzRankFour
set_option autoImplicit false
noncomputable section
open Math LorentzFiniteControls LorentzDirections
variable (b : Tensor)
  (h : ∀ g u v w x, b (direction g u) (direction g v)
    (direction g w) (direction g x) = b u v w x)
  (hs : ∀ u v w x, b u v w x = b v u w x)

include h hs in
theorem components20 (k l : Fin 4) :
    component b 2 0 k l = -component b 0 0 1 1*(metric 2 0*metric k l) - component b 0 1 0 1*(metric 2 k*metric 0 l+metric 2 l*metric 0 k) := by
  fin_cases k <;> fin_cases l
  all_goals rw [normalize b h hs]
  all_goals norm_num [normalComponent,killed,signsZ,signsX,metric,← component_apply,
    value0000 b h hs,value0022 b h hs,value0033 b h hs,value0110 b h hs,value0123 b h hs,value0132 b h hs,value0202 b h hs,value0213 b h hs,value0220 b h hs,value0231 b h hs,value0303 b h hs,value0312 b h hs,value0321 b h hs,value0330 b h hs,value1100 b h hs,value1111 b h hs,value1122 b h hs,value1133 b h hs,value1203 b h hs,value1212 b h hs,value1221 b h hs,value1230 b h hs,value1302 b h hs,value1313 b h hs,value1320 b h hs,value1331 b h hs,value2200 b h hs,value2211 b h hs,value2222 b h hs,value2233 b h hs,value2301 b h hs,value2310 b h hs,value2323 b h hs,value2332 b h hs,value3300 b h hs,value3311 b h hs,value3322 b h hs,value3333 b h hs]


include h hs in
theorem components21 (k l : Fin 4) :
    component b 2 1 k l = -component b 0 0 1 1*(metric 2 1*metric k l) - component b 0 1 0 1*(metric 2 k*metric 1 l+metric 2 l*metric 1 k) := by
  fin_cases k <;> fin_cases l
  all_goals rw [normalize b h hs]
  all_goals norm_num [normalComponent,killed,signsZ,signsX,metric,← component_apply,
    value0000 b h hs,value0022 b h hs,value0033 b h hs,value0110 b h hs,value0123 b h hs,value0132 b h hs,value0202 b h hs,value0213 b h hs,value0220 b h hs,value0231 b h hs,value0303 b h hs,value0312 b h hs,value0321 b h hs,value0330 b h hs,value1100 b h hs,value1111 b h hs,value1122 b h hs,value1133 b h hs,value1203 b h hs,value1212 b h hs,value1221 b h hs,value1230 b h hs,value1302 b h hs,value1313 b h hs,value1320 b h hs,value1331 b h hs,value2200 b h hs,value2211 b h hs,value2222 b h hs,value2233 b h hs,value2301 b h hs,value2310 b h hs,value2323 b h hs,value2332 b h hs,value3300 b h hs,value3311 b h hs,value3322 b h hs,value3333 b h hs]


include h hs in
theorem components22 (k l : Fin 4) :
    component b 2 2 k l = -component b 0 0 1 1*(metric 2 2*metric k l) - component b 0 1 0 1*(metric 2 k*metric 2 l+metric 2 l*metric 2 k) := by
  fin_cases k <;> fin_cases l
  all_goals rw [normalize b h hs]
  all_goals norm_num [normalComponent,killed,signsZ,signsX,metric,← component_apply,
    value0000 b h hs,value0022 b h hs,value0033 b h hs,value0110 b h hs,value0123 b h hs,value0132 b h hs,value0202 b h hs,value0213 b h hs,value0220 b h hs,value0231 b h hs,value0303 b h hs,value0312 b h hs,value0321 b h hs,value0330 b h hs,value1100 b h hs,value1111 b h hs,value1122 b h hs,value1133 b h hs,value1203 b h hs,value1212 b h hs,value1221 b h hs,value1230 b h hs,value1302 b h hs,value1313 b h hs,value1320 b h hs,value1331 b h hs,value2200 b h hs,value2211 b h hs,value2222 b h hs,value2233 b h hs,value2301 b h hs,value2310 b h hs,value2323 b h hs,value2332 b h hs,value3300 b h hs,value3311 b h hs,value3322 b h hs,value3333 b h hs]
  all_goals ring


include h hs in
theorem components23 (k l : Fin 4) :
    component b 2 3 k l = -component b 0 0 1 1*(metric 2 3*metric k l) - component b 0 1 0 1*(metric 2 k*metric 3 l+metric 2 l*metric 3 k) := by
  fin_cases k <;> fin_cases l
  all_goals rw [normalize b h hs]
  all_goals norm_num [normalComponent,killed,signsZ,signsX,metric,← component_apply,
    value0000 b h hs,value0022 b h hs,value0033 b h hs,value0110 b h hs,value0123 b h hs,value0132 b h hs,value0202 b h hs,value0213 b h hs,value0220 b h hs,value0231 b h hs,value0303 b h hs,value0312 b h hs,value0321 b h hs,value0330 b h hs,value1100 b h hs,value1111 b h hs,value1122 b h hs,value1133 b h hs,value1203 b h hs,value1212 b h hs,value1221 b h hs,value1230 b h hs,value1302 b h hs,value1313 b h hs,value1320 b h hs,value1331 b h hs,value2200 b h hs,value2211 b h hs,value2222 b h hs,value2233 b h hs,value2301 b h hs,value2310 b h hs,value2323 b h hs,value2332 b h hs,value3300 b h hs,value3311 b h hs,value3322 b h hs,value3333 b h hs]

end
end Physics.LorentzRankFour
