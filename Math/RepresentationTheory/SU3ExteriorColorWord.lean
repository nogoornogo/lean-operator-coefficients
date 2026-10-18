import Math.RepresentationTheory.SU3ColorTensorWord
import Math.RepresentationTheory.SU3DualExterior

/-! Exact positive coupling for arbitrary words of exterior-restricted
defining and dual color factors. Capacity and complementary duality are
proved on the actual quotients before the tensor-word triality rule is used.
This does not cover symmetric or higher Young-restricted color factors. -/
namespace Math.SU3ExteriorColorWord
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior InvariantCoefficientProduct
open scoped TensorProduct
abbrev Data := SU3ColorTensorWord.Data

inductive Word
  | empty
  | exterior (degree : ℕ)
  | dualExterior (degree : ℕ)
  | tensor (left right : Word)

@[reducible] def data : Word → Data
  | .empty => { Carrier := ℂ,action := trivial ℂ Group ℂ }
  | .exterior n => { Carrier := ⋀[ℂ]^n Vector,action := rho.exteriorPower n }
  | .dualExterior n =>
    { Carrier := ⋀[ℂ]^n (Module.Dual ℂ Vector),action := rho.dual.exteriorPower n }
  | .tensor l r =>
    { Carrier := (data l).Carrier ⊗[ℂ] (data r).Carrier
      action := (data l).action.tprod (data r).action }

abbrev Carrier (w : Word) := (data w).Carrier
abbrev action (w : Word) := (data w).action

def Fits : Word → Prop
  | .empty => True
  | .exterior n => n≤3
  | .dualExterior n => n≤3
  | .tensor l r => Fits l ∧ Fits r

def reduced : Word → SU3ColorTensorWord.Word
  | .empty => .empty
  | .exterior 1 => .defining
  | .exterior 2 => .dual
  | .exterior _ => .empty
  | .dualExterior 1 => .dual
  | .dualExterior 2 => .defining
  | .dualExterior _ => .empty
  | .tensor l r => .tensor (reduced l) (reduced r)

def exteriorEquiv (n : ℕ) (hn : n≤3) :
    Representation.Equiv (action (.exterior n)) (SU3ColorTensorWord.action (reduced (.exterior n))) := by
  interval_cases n
  · exact rho.exteriorPowerZeroEquiv
  · exact rho.exteriorPowerOneEquiv
  · exact SU3DefiningExterior.twoEquiv
  · exact SU3DefiningExterior.topEquiv

def dualExteriorEquiv (n : ℕ) (hn : n≤3) :
    Representation.Equiv (action (.dualExterior n))
      (SU3ColorTensorWord.action (reduced (.dualExterior n))) := by
  interval_cases n
  · exact rho.dual.exteriorPowerZeroEquiv
  · exact rho.dual.exteriorPowerOneEquiv
  · exact SU3DualExterior.twoEquiv
  · exact SU3DualExterior.topEquiv

/-- The actual quotient word reduces to its defining/dual word, only after
each exterior factor has passed the proved capacity bound. -/
def equivalence : (w : Word) → Fits w →
    Representation.Equiv (action w) (SU3ColorTensorWord.action (reduced w))
  | .empty,_ => .refl _
  | .exterior n,h => exteriorEquiv n h
  | .dualExterior n,h => dualExteriorEquiv n h
  | .tensor l r,h => ExternalInvariantTensor.tensorEquiv
      (equivalence l h.1) (equivalence r h.2)

/-- An over-capacity exterior factor kills the entire tensor word. -/
theorem zero_of_not_fits : (w : Word) → ¬ Fits w → ∀ x : Carrier w, x=0
  | .empty,h,_ => (h trivial).elim
  | .exterior n,h,x => SU3DefiningExterior.high_zero n (by exact Nat.lt_of_not_ge h) x
  | .dualExterior n,h,x => exteriorPower.eq_zero_of_finrank_lt n (by
      rw [Subspace.dual_finrank_eq,SU3DefiningExterior.dimension]
      exact Nat.lt_of_not_ge h) x
  | .tensor l r,h,x => by
    classical
    by_cases hl : Fits l
    · have hr : ¬ Fits r := fun hr => h ⟨hl,hr⟩
      induction x using TensorProduct.inductionOn with
      | tmul a b => rw [zero_of_not_fits r hr b,TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx,hy,add_zero]
    · induction x using TensorProduct.inductionOn with
      | tmul a b => rw [zero_of_not_fits l hl a,TensorProduct.zero_tmul]
      | add x y hx hy => rw [hx,hy,add_zero]

theorem allowed_iff (w : Word) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (action w)) ↔
      Fits w ∧ SU3ColorTensorWord.positiveCount (reduced w)%3=
        SU3ColorTensorWord.negativeCount (reduced w)%3 := by
  classical
  by_cases h : Fits w
  · rw [SelectionCriteria.allowed_equiv
      (InvariantCoefficientTransport.alongEquiv (equivalence w h)),
      SU3ColorTensorWord.allowed_iff]
    simp only [h,true_and]
  · constructor
    · rintro ⟨f,hf⟩
      exact (hf (by
        apply IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rw [zero_of_not_fits w h x,map_zero]
        rfl)).elim
    · exact fun hh => (h hh.1).elim

theorem forbidden_iff (w : Word) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants (action w)) ↔
      ¬ Fits w ∨ SU3ColorTensorWord.positiveCount (reduced w)%3≠
        SU3ColorTensorWord.negativeCount (reduced w)%3 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed,allowed_iff,not_and_or]

end
end Math.SU3ExteriorColorWord
