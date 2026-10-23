import Physics.FieldTheory.Jets.LorentzRankFour.Core.Rows4

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
theorem value3333 : component b 3 3 3 3 = (-1/1 : ℂ)*component b 0 0 1 1 + (-2/1 : ℂ)*component b 0 1 0 1 := by
  have he := row35 b h hs
  linear_combination he

include h hs in
theorem value3322 : component b 3 3 2 2 = (-1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row37 b h hs
  linear_combination he

include h hs in
theorem value3311 : component b 3 3 1 1 = (-1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row7 b h hs
  linear_combination he

include h hs in
theorem value3300 : component b 3 3 0 0 = (1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row34 b h hs
  rw [value3333 b h hs,value3311 b h hs] at he
  linear_combination he

include h hs in
theorem value2332 : component b 2 3 3 2 = (-1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row33 b h hs
  linear_combination he

include h hs in
theorem value2323 : component b 2 3 2 3 = (-1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row24 b h hs
  linear_combination he

include h hs in
theorem value2310 : component b 2 3 1 0 = 0 := by
  have he := row9 b h hs
  linear_combination he

include h hs in
theorem value2301 : component b 2 3 0 1 = 0 := by
  have he := row8 b h hs
  linear_combination he

include h hs in
theorem value2233 : component b 2 2 3 3 = (-1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row25 b h hs
  rw [value3311 b h hs] at he
  linear_combination he

include h hs in
theorem value2222 : component b 2 2 2 2 = (-1/1 : ℂ)*component b 0 0 1 1 + (-2/1 : ℂ)*component b 0 1 0 1 := by
  have he := row32 b h hs
  rw [value3322 b h hs,value2332 b h hs] at he
  linear_combination he

include h hs in
theorem value2211 : component b 2 2 1 1 = (-1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row18 b h hs
  rw [value3311 b h hs] at he
  linear_combination he

include h hs in
theorem value2200 : component b 2 2 0 0 = (1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row17 b h hs
  rw [value2233 b h hs] at he
  linear_combination he

include h hs in
theorem value1331 : component b 1 3 3 1 = (-1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row6 b h hs
  linear_combination he

include h hs in
theorem value1320 : component b 1 3 2 0 = 0 := by
  have he := row16 b h hs
  linear_combination he

include h hs in
theorem value1313 : component b 1 3 1 3 = (-1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row23 b h hs
  rw [value2332 b h hs] at he
  linear_combination he

include h hs in
theorem value1302 : component b 1 3 0 2 = 0 := by
  have he := row15 b h hs
  linear_combination he

include h hs in
theorem value1230 : component b 1 2 3 0 = 0 := by
  have he := row27 b h hs
  rw [value1302 b h hs,value1320 b h hs] at he
  linear_combination he

include h hs in
theorem value1221 : component b 1 2 2 1 = (-1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row19 b h hs
  rw [value1331 b h hs] at he
  linear_combination he

include h hs in
theorem value1212 : component b 1 2 1 2 = (-1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row20 b h hs
  rw [value1313 b h hs] at he
  linear_combination he

include h hs in
theorem value1203 : component b 1 2 0 3 = 0 := by
  have he := row26 b h hs
  rw [value1230 b h hs,value1302 b h hs,value1320 b h hs] at he
  linear_combination he

include h hs in
theorem value1133 : component b 1 1 3 3 = (-1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row22 b h hs
  rw [value3322 b h hs] at he
  linear_combination he

include h hs in
theorem value1122 : component b 1 1 2 2 = (-1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row21 b h hs
  rw [value1133 b h hs] at he
  linear_combination he

include h hs in
theorem value1111 : component b 1 1 1 1 = (-1/1 : ℂ)*component b 0 0 1 1 + (-2/1 : ℂ)*component b 0 1 0 1 := by
  have he := row36 b h hs
  rw [value1133 b h hs,value3311 b h hs,value2200 b h hs,value2222 b h hs,value2233 b h hs,value3322 b h hs,value1313 b h hs,value2332 b h hs,value2323 b h hs] at he
  linear_combination he

include h hs in
theorem value1100 : component b 1 1 0 0 = (1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row4 b h hs
  rw [value1133 b h hs] at he
  linear_combination he

include h hs in
theorem value0330 : component b 0 3 3 0 = (1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row31 b h hs
  rw [value2332 b h hs,value2323 b h hs,value2222 b h hs,value3322 b h hs] at he
  linear_combination he

include h hs in
theorem value0321 : component b 0 3 2 1 = 0 := by
  have he := row3 b h hs
  linear_combination he

include h hs in
theorem value0312 : component b 0 3 1 2 = 0 := by
  have he := row2 b h hs
  linear_combination he

include h hs in
theorem value0303 : component b 0 3 0 3 = (1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row30 b h hs
  rw [value2222 b h hs,value3322 b h hs,value2332 b h hs] at he
  linear_combination he

include h hs in
theorem value0231 : component b 0 2 3 1 = 0 := by
  have he := row0 b h hs
  rw [value0321 b h hs] at he
  linear_combination he

include h hs in
theorem value0220 : component b 0 2 2 0 = (1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row14 b h hs
  rw [value2323 b h hs] at he
  linear_combination he

include h hs in
theorem value0213 : component b 0 2 1 3 = 0 := by
  have he := row1 b h hs
  rw [value0312 b h hs] at he
  linear_combination he

include h hs in
theorem value0202 : component b 0 2 0 2 = (1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row13 b h hs
  rw [value2332 b h hs] at he
  linear_combination he

include h hs in
theorem value0132 : component b 0 1 3 2 = 0 := by
  have he := row10 b h hs
  rw [value0312 b h hs] at he
  linear_combination he

include h hs in
theorem value0123 : component b 0 1 2 3 = 0 := by
  have he := row11 b h hs
  rw [value0321 b h hs] at he
  linear_combination he

include h hs in
theorem value0110 : component b 0 1 1 0 = (1/1 : ℂ)*component b 0 1 0 1 := by
  have he := row5 b h hs
  rw [value1313 b h hs] at he
  linear_combination he

include h hs in
theorem value0033 : component b 0 0 3 3 = (1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row29 b h hs
  rw [value0202 b h hs,value0303 b h hs,value2222 b h hs,value2233 b h hs,value3322 b h hs,value3333 b h hs] at he
  linear_combination he

include h hs in
theorem value0022 : component b 0 0 2 2 = (1/1 : ℂ)*component b 0 0 1 1 := by
  have he := row12 b h hs
  rw [value3322 b h hs] at he
  linear_combination he

include h hs in
theorem value0000 : component b 0 0 0 0 = (-1/1 : ℂ)*component b 0 0 1 1 + (-2/1 : ℂ)*component b 0 1 0 1 := by
  have he := row28 b h hs
  rw [value0022 b h hs,value0033 b h hs,value0202 b h hs,value0220 b h hs,value0303 b h hs,value0330 b h hs,value2200 b h hs,value2222 b h hs,value2233 b h hs,value3300 b h hs,value3322 b h hs,value3333 b h hs] at he
  linear_combination he

end
end Physics.LorentzRankFour
