import Math.Lean.Compatibility

/-! Compatibility controls for polymorphic types, construction, field notation,
patterns, coercions, typeclass search, simp and executable data. -/

namespace Physics.SourceCompatibilityControl
universe u
structure Box (α : Type u) where
  value : α
  deriving DecidableEq
instance {α : Type u} : Coe (Box α) α := ⟨Box.value⟩
@[simp] theorem value_mk {α : Type u} (x : α) : (Box.mk x).value = x := rfl
def Box.map {α β : Type u} (f : α → β) (b : Box α) : Box β := ⟨f b.value⟩
end Physics.SourceCompatibilityControl

-- Deliberately put the projection before its type: dependencies determine order.
compatibility_aliases [
  GUT.SourceCompatibilityControl.Box.value => Physics.SourceCompatibilityControl.Box.value,
  GUT.SourceCompatibilityControl.Box.map => Physics.SourceCompatibilityControl.Box.map,
  GUT.SourceCompatibilityControl.Box.mk => Physics.SourceCompatibilityControl.Box.mk,
  GUT.SourceCompatibilityControl.Box.casesOn => Physics.SourceCompatibilityControl.Box.casesOn,
  GUT.SourceCompatibilityControl.Box.rec => Physics.SourceCompatibilityControl.Box.rec,
  GUT.SourceCompatibilityControl.Box.recOn => Physics.SourceCompatibilityControl.Box.recOn,
  GUT.SourceCompatibilityControl.Box.noConfusion => Physics.SourceCompatibilityControl.Box.noConfusion,
  GUT.SourceCompatibilityControl.Box => Physics.SourceCompatibilityControl.Box,
  GUT.SourceCompatibilityControl.value_mk => Physics.SourceCompatibilityControl.value_mk
]

example : DecidableEq (GUT.SourceCompatibilityControl.Box Nat) := inferInstance
example : GUT.SourceCompatibilityControl.Box Nat := { value := 3 }
example (x : Nat) : (GUT.SourceCompatibilityControl.Box.mk x).value = x := by simp
example (b : GUT.SourceCompatibilityControl.Box Nat) : b.value = b.value := rfl
example (b : GUT.SourceCompatibilityControl.Box Nat) : (b : Nat) = b.value := rfl
example (b : GUT.SourceCompatibilityControl.Box Nat) : b = b := by cases b; rfl
example (b : GUT.SourceCompatibilityControl.Box Nat) : b = b := by
  cases b using GUT.SourceCompatibilityControl.Box.casesOn
  rfl
example (b : GUT.SourceCompatibilityControl.Box Nat) : b = b := by
  induction b using GUT.SourceCompatibilityControl.Box.rec with
  | mk x => rfl
example (b : GUT.SourceCompatibilityControl.Box Nat) : { b with value := b.value } = b := by
  cases b
  rfl
example : (match GUT.SourceCompatibilityControl.Box.mk 3 with
    | GUT.SourceCompatibilityControl.Box.mk x => x) = 3 := rfl
example : (GUT.SourceCompatibilityControl.Box.map Nat.succ
    (GUT.SourceCompatibilityControl.Box.mk 3)).value = 4 := rfl
section
open GUT.SourceCompatibilityControl
example : Box Nat := ⟨3⟩
end
namespace Physics.SourceCompatibilityControl.ExportTest
export GUT.SourceCompatibilityControl (Box)
example : Box Nat := ⟨3⟩
end Physics.SourceCompatibilityControl.ExportTest
#eval (GUT.SourceCompatibilityControl.Box.mk 7).value
#eval GUT.SourceCompatibilityControl.Box.casesOn
  (motive := fun _ : GUT.SourceCompatibilityControl.Box Nat => Nat)
  (GUT.SourceCompatibilityControl.Box.mk 9) (fun n => n)

namespace Physics.SourceCompatibilityControl
def firstTarget : Nat := 1
def secondTarget : Nat := 2
def wrongAlias : Nat := firstTarget
end Physics.SourceCompatibilityControl

/-- error: Compatibility value changed: Physics.SourceCompatibilityControl.wrongAlias / Physics.SourceCompatibilityControl.secondTarget -/
#guard_msgs in
assert_compatible Physics.SourceCompatibilityControl.wrongAlias => Physics.SourceCompatibilityControl.secondTarget
