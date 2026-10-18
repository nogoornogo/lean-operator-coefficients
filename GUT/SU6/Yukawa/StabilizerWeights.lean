import Math.RepresentationTheory.ExteriorSquareCoordinates
import Mathlib.Data.ZMod.Basic

open Math

/-! Exact finite weight separation for the four vacuum-preserving phases.
This is a finite combinatorial certificate, not yet a basis transport theorem. -/
set_option autoImplicit false
namespace GUT.SU6YukawaWeights

abbrev Label := (ExteriorSquareCoordinates.Pair 6 ⊕ Fin 6) ⊕ Fin 6

def fundamental (k : Fin 4) (i : Fin 6) : ZMod 4 :=
  if i.val = k.val then 1 else if i.val = 4 then -1 else 0

def weight (k : Fin 4) : Label → ZMod 4
  | .inl (.inl p) => fundamental k p.val.1 + fundamental k p.val.2
  | .inl (.inr i) => -fundamental k i
  | .inr i => -fundamental k i

def dualIndex : Label → Option (Fin 6)
  | .inl (.inl _) => none
  | .inl (.inr i) => some i
  | .inr i => some i

def pairs (p : ExteriorSquareCoordinates.Pair 6) (j : Label) : Prop :=
  p.val.2 = 5 ∧ dualIndex j = some p.val.1

def allowed (i j : Label) : Prop :=
  match i, j with
  | .inl (.inl p), j => pairs p j
  | i, .inl (.inl p) => pairs p i
  | i, j => dualIndex i = some 5 ∧ dualIndex j = some 5

def wedgeFive (i : Fin 5) : ExteriorSquareCoordinates.Pair 6 :=
  ⟨(i.castSucc, 5), i.isLt⟩

def exteriorLabel (i : Fin 5) : Label := .inl (.inl (wedgeFive i))

def dualLabel (c : Bool) (i : Fin 6) : Label :=
  if c then .inr i else .inl (.inr i)

instance (i j : Label) : Decidable (allowed i j) := by
  unfold allowed pairs
  split <;> infer_instance

theorem allowed_cases : ∀ i j : Label, allowed i j →
    (∃ (a : Fin 5) (c : Bool), i = exteriorLabel a ∧ j = dualLabel c a.castSucc) ∨
    (∃ (a : Fin 5) (c : Bool), j = exteriorLabel a ∧ i = dualLabel c a.castSucc) ∨
    (∃ c d : Bool, i = dualLabel c 5 ∧ j = dualLabel d 5) := by
  let : DecidableEq Label := inferInstance
  let : Fintype Label := inferInstance
  decide

theorem separation : ∀ i j : Label,
    (∀ k : Fin 4, weight k i + weight k j = 0) ↔ allowed i j := by
  decide

noncomputable def character (a : ZMod 4) : ℂ := Complex.I ^ a.val

theorem character_add (a b : ZMod 4) :
    character (a + b) = character a * character b := by
  simp only [character, ZMod.val_add]
  fin_cases a <;> fin_cases b <;>
    norm_num [ZMod.val, pow_succ, Complex.I_mul_I]

theorem character_eq_one (a : ZMod 4) : character a = 1 ↔ a = 0 := by
  rw [← ZMod.val_eq_zero]
  fin_cases a <;>
    norm_num [character, ZMod.val, pow_succ, Complex.I_mul_I, Complex.ext_iff]

theorem character_neg (a : ZMod 4) : character (-a) * character a = 1 := by
  rw [← character_add, neg_add_cancel]
  norm_num [character]

theorem allowed_iff (i j : Label) :
    (∀ k : Fin 4, character (weight k i) * character (weight k j) = 1) ↔
      allowed i j := by
  simp only [← character_add, character_eq_one]
  exact separation i j

end GUT.SU6YukawaWeights
