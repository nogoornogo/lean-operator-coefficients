import Physics.FieldTheory.Jets.LorentzRankFour.Core.Components3

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
theorem components (i j k l : Fin 4) :
    component b i j k l = -component b 0 0 1 1*(metric i j*metric k l) - component b 0 1 0 1*(metric i k*metric j l+metric i l*metric j k) := by
  fin_cases i <;> fin_cases j
  · exact components00 b h hs k l
  · exact components01 b h hs k l
  · exact components02 b h hs k l
  · exact components03 b h hs k l
  · exact components10 b h hs k l
  · exact components11 b h hs k l
  · exact components12 b h hs k l
  · exact components13 b h hs k l
  · exact components20 b h hs k l
  · exact components21 b h hs k l
  · exact components22 b h hs k l
  · exact components23 b h hs k l
  · exact components30 b h hs k l
  · exact components31 b h hs k l
  · exact components32 b h hs k l
  · exact components33 b h hs k l

end
end Physics.LorentzRankFour
