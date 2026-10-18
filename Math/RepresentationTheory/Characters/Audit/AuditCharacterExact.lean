import Math.RepresentationTheory.Characters.CharacterExact
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# An exact character sequence that does not split equivariantly

The additive rational group acts on two coordinates by `(x,y) -> (x+a*y,y)`.
Inclusion of the first axis and projection to the second coordinate form an
exact sequence of representations with trivial outer terms. No equivariant
right inverse to the projection exists. Character additivity and the two
signed indices still hold, without any invariant-complement hypothesis.
-/

namespace Math.AuditCharacterExact

open CharacterExact

noncomputable section

abbrev ActingGroup := Multiplicative ℚ

def trivial : Representation ℚ ActingGroup ℚ :=
  Representation.trivial ℚ ActingGroup ℚ

def shear : Representation ℚ ActingGroup (ℚ × ℚ) where
  toFun a := (LinearMap.fst ℚ ℚ ℚ + a.toAdd • LinearMap.snd ℚ ℚ ℚ).prod
    (LinearMap.snd ℚ ℚ ℚ)
  map_one' := by ext <;> simp
  map_mul' a b := by
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · change x.1 + (a.toAdd + b.toAdd) * x.2 =
        x.1 + b.toAdd * x.2 + a.toAdd * x.2
      ring
    · rfl

@[simp]
theorem shear_apply (a : ActingGroup) (v : ℚ × ℚ) :
    shear a v = (v.1 + a.toAdd * v.2, v.2) := rfl

def inclusion : trivial.IntertwiningMap shear where
  toLinearMap := LinearMap.inl ℚ ℚ ℚ
  isIntertwining' a := by ext <;> simp [trivial, Representation.trivial]

def projection : shear.IntertwiningMap trivial where
  toLinearMap := LinearMap.snd ℚ ℚ ℚ
  isIntertwining' _ := rfl

theorem inclusion_injective : Function.Injective inclusion := by
  intro x y h
  exact congrArg Prod.fst h

theorem projection_surjective : Function.Surjective projection :=
  fun y => ⟨(0, y), rfl⟩

theorem sequence_exact : Function.Exact inclusion projection := by
  intro x
  change x.2 = 0 ↔ ∃ y : ℚ, (y, 0) = x
  constructor
  · intro hx
    exact ⟨x.1, Prod.ext rfl hx.symm⟩
  · rintro ⟨y, rfl⟩
    rfl

/-- The extension has no equivariant splitting, despite vector-space splitting. -/
theorem no_equivariant_section :
    ¬ ∃ s : trivial.IntertwiningMap shear, ∀ x, projection (s x) = x := by
  rintro ⟨s, hs⟩
  have hfirst := congrArg Prod.fst
    (Representation.IntertwiningMap.isIntertwining trivial shear s
      (Multiplicative.ofAdd 1) 1)
  have hsecond : (s 1).2 = 1 := hs 1
  change (s 1).1 = (s 1).1 + 1 * (s 1).2 at hfirst
  rw [one_mul, hsecond] at hfirst
  simp at hfirst

theorem trivial_character (g : ActingGroup) : trivial.character g = 1 := by
  simp [trivial, Representation.character, Representation.trivial]

theorem shear_character (g : ActingGroup) : shear.character g = 2 := by
  rw [character_eq_add_of_exact inclusion projection inclusion_injective
    projection_surjective sequence_exact g, trivial_character]
  norm_num

/-- A surjective map with a one-dimensional kernel has positive index. -/
theorem projection_index (g : ActingGroup) : indexCharacter projection g = 1 := by
  rw [indexCharacter_eq_source_sub_target, shear_character, trivial_character]
  norm_num

/-- The inclusion has the opposite index, coming from its quotient cokernel. -/
theorem inclusion_index (g : ActingGroup) : indexCharacter inclusion g = -1 := by
  rw [indexCharacter_eq_source_sub_target, shear_character, trivial_character]
  norm_num

#print axioms CharacterExact.character_eq_add_of_exact
#print axioms CharacterExact.character_eq_sub_add_quotient
#print axioms CharacterExact.complementQuotientEquiv
#print axioms CharacterExact.character_eq_kernel_add_range
#print axioms CharacterExact.indexCharacter_eq_source_sub_target
#print axioms no_equivariant_section
#print axioms projection_index
#print axioms inclusion_index

end

end Math.AuditCharacterExact
