import Math.RepresentationTheory.Characters.CompactVirtualCharacter

/-! Merge equal characters in a finite irreducible family. This is a
noncomputable normalization, not an algorithm for classifying representations. -/

namespace Math.NormalizedCharacterFamily
noncomputable section
open Representation ContinuousRepresentationScope
open scoped BigOperators

variable {H J : Type*} [Group H] [Fintype J]
  {V : J → Type*} [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℂ (V j)]
  [∀ j, FiniteDimensional ℂ (V j)] (S : ∀ j, Representation ℂ H (V j))

def Index := Set.range (fun j => (S j).character)

instance : Finite (Index S) := Set.finite_range _ |>.to_subtype
instance : Fintype (Index S) := Fintype.ofFinite _

def representative (i : Index S) : J := i.property.choose

omit [Fintype J] [∀ j, FiniteDimensional ℂ (V j)] in
theorem representative_character (i : Index S) :
    (S (representative S i)).character = i.val := i.property.choose_spec

abbrev Carrier (i : Index S) := V (representative S i)
def action (i : Index S) : Representation ℂ H (Carrier S i) := S (representative S i)

instance [∀ j, IsIrreducible (S j)] (i : Index S) : IsIrreducible (action S i) :=
  inferInstanceAs (IsIrreducible (S (representative S i)))

omit [Fintype J] [∀ j, FiniteDimensional ℂ (V j)] in
theorem inequivalent (i k : Index S) (hne : i ≠ k) :
    IsEmpty (Representation.Equiv (action S i) (action S k)) := by
  refine ⟨fun e => hne (Subtype.ext ?_)⟩
  exact (representative_character S i).symm.trans
    ((char_iso e).trans (representative_character S k))

omit [Fintype J] [∀ j, FiniteDimensional ℂ (V j)] in
theorem continuous [TopologicalSpace H] (hc : ∀ j, IsJointlyContinuous (S j))
    (i : Index S) : IsJointlyContinuous (action S i) := hc _

def classOf (j : J) : Index S := ⟨(S j).character, ⟨j, rfl⟩⟩

def coefficients (a : J → ℤ) (i : Index S) : ℤ := by
  classical
  exact ∑ j, if classOf S j = i then a j else 0

omit [∀ j, FiniteDimensional ℂ (V j)] in
theorem character (a : J → ℤ) (h : H) :
    CompactVirtualCharacter.character (action S) (coefficients S a) h =
      CompactVirtualCharacter.character S a h := by
  classical
  simp only [CompactVirtualCharacter.character, coefficients, Int.cast_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (classOf S j)]
  · simp only [ite_true, action]
    rw [representative_character]
    rfl
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

end
end Math.NormalizedCharacterFamily
