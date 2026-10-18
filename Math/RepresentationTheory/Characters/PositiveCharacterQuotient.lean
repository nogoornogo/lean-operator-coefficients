import Mathlib.RepresentationTheory.Character
import Mathlib.Tactic.NormNum

/-!
# Positive character content produces actual irreducible quotients

For finite groups in characteristic zero, a character identity
`chi(L) = chi(S) + chi(R)` with R irreducible yields an actual equivariant
surjection L -> R. S is an actual representation, not an arbitrary signed
class function. The proof uses mathlib's character/Hom dimension formula.
-/

set_option autoImplicit false

namespace Math.PositiveCharacterQuotient

noncomputable section

open Representation Module
open scoped BigOperators

variable {k H L S R U : Type*} [Field k] [CharZero k] [Group H] [Fintype H]
  [AddCommGroup L] [Module k L] [FiniteDimensional k L]
  [AddCommGroup S] [Module k S] [FiniteDimensional k S]
  [AddCommGroup R] [Module k R] [FiniteDimensional k R]
  [AddCommGroup U] [Module k U] [FiniteDimensional k U]

theorem hom_finrank_add (rho : Representation k H L) (sigma : Representation k H S)
    (tau : Representation k H R) (upsilon : Representation k H U)
    (hc : ∀ g, rho.character g = sigma.character g + tau.character g) :
    finrank k (IntertwiningMap rho upsilon) =
      finrank k (IntertwiningMap sigma upsilon) + finrank k (IntertwiningMap tau upsilon) := by
  have hcard : (Nat.card H : k) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let := invertibleOfNonzero hcard
  have he : (finrank k (IntertwiningMap rho upsilon) : k) =
      (finrank k (IntertwiningMap sigma upsilon) : k) +
        (finrank k (IntertwiningMap tau upsilon) : k) := by
    rw [← card_inv_mul_sum_char_mul_char_eq_finrank rho upsilon,
      ← card_inv_mul_sum_char_mul_char_eq_finrank sigma upsilon,
      ← card_inv_mul_sum_char_mul_char_eq_finrank tau upsilon]
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib, mul_add]
  exact_mod_cast he

/-- A constituent already detected in the positive contribution can be
extracted from the actual source. No classification of irreducibles is used. -/
theorem exists_surjective_of_character_add_of_nonzero
    (rho : Representation k H L) (sigma : Representation k H S)
    (tau : Representation k H R) (upsilon : Representation k H U)
    [IsIrreducible upsilon]
    (hc : ∀ g, rho.character g = sigma.character g + tau.character g)
    (f : IntertwiningMap tau upsilon) (hf : f ≠ 0) :
    ∃ p : IntertwiningMap rho upsilon, Function.Surjective p := by
  have hd := hom_finrank_add rho sigma tau upsilon hc
  have hp : 0 < finrank k (IntertwiningMap tau upsilon) := by
    let : Nontrivial (IntertwiningMap tau upsilon) := nontrivial_of_ne f 0 hf
    exact finrank_pos
  have hl : 0 < finrank k (IntertwiningMap rho upsilon) := by omega
  let : Nontrivial (IntertwiningMap rho upsilon) := finrank_pos_iff.mp hl
  obtain ⟨p, hp⟩ := exists_ne (0 : IntertwiningMap rho upsilon)
  exact ⟨p, (IsIrreducible.surjective_or_eq_zero p).resolve_right hp⟩

/-- Positivity is supplied by an actual remainder S; no character-equivalence
classification or assumed projection certificate is used. -/
theorem exists_surjective_of_character_add [IsAlgClosed k]
    (rho : Representation k H L) (sigma : Representation k H S)
    (tau : Representation k H R) [IsIrreducible tau]
    (hc : ∀ g, rho.character g = sigma.character g + tau.character g) :
    ∃ f : IntertwiningMap rho tau, Function.Surjective f := by
  have hd := hom_finrank_add rho sigma tau tau hc
  rw [IsIrreducible.finrank_intertwiningMap_self] at hd
  have hp : 0 < finrank k (IntertwiningMap rho tau) := by omega
  let : Nontrivial (IntertwiningMap rho tau) := (finrank_pos_iff).mp hp
  obtain ⟨f, hf⟩ := exists_ne (0 : IntertwiningMap rho tau)
  exact ⟨f, (IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩

end
end Math.PositiveCharacterQuotient
