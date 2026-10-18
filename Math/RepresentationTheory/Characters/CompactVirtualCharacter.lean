import Math.RepresentationTheory.Characters.CompactHomDimension
import Math.RepresentationTheory.Decomposition.CompactIrreducibleQuotient

/-! Normalized finite virtual characters of compact groups. Negative
coefficients are allowed; positive dimension supplies a positive constituent,
and character/Hom counting extracts it from actual differences of characters. -/

namespace Math.CompactVirtualCharacter
noncomputable section
open scoped BigOperators
open Representation ContinuousRepresentationScope MeasureTheory SplitRepresentationProjection

variable {H I : Type*} [Group H] [Fintype I]
  {V : I → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
  [∀ i, FiniteDimensional ℂ (V i)]
  (S : ∀ i, Representation ℂ H (V i)) (a : I → ℤ)

def character (h : H) : ℂ := ∑ i, (a i : ℂ) * (S i).character h

def dimension : ℤ := ∑ i, a i * (Module.finrank ℂ (V i) : ℤ)

theorem character_one : character S a 1 = (dimension (V := V) a : ℂ) := by
  simp [character, dimension, char_one]

theorem dimension_pos_of_actual {L : Type*} [AddCommGroup L] [Module ℂ L]
    [FiniteDimensional ℂ L] [Nontrivial L] (rho : Representation ℂ H L)
    (he : ∀ h, rho.character h = character S a h) : 0 < dimension (V := V) a := by
  have h := he 1
  rw [char_one, character_one] at h
  have hn : (Module.finrank ℂ L : ℤ) = dimension (V := V) a := by exact_mod_cast h
  rw [← hn]
  exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℂ L)

omit [∀ i, FiniteDimensional ℂ (V i)] in
theorem exists_positive (hd : 0 < dimension (V := V) a) :
    ∃ i, 0 < a i ∧ 0 < Module.finrank ℂ (V i) := by
  have hx : ∃ i, 0 < a i * (Module.finrank ℂ (V i) : ℤ) := by
    by_contra hh
    push Not at hh
    exact (not_le_of_gt hd) (Finset.sum_nonpos fun i _ => hh i)
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_, ?_⟩
  · by_contra hn
    have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn)
      (Int.natCast_nonneg (Module.finrank ℂ (V i)))
    omega
  · by_contra hn
    have hz : Module.finrank ℂ (V i) = 0 := by omega
    simp [hz] at hi

variable [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [MeasurableSpace H] [BorelSpace H]
  [∀ i, IsIrreducible (S i)]
  (hc : ∀ i, IsJointlyContinuous (S i))
  (hn : ∀ i j, i ≠ j → IsEmpty (Representation.Equiv (S i) (S j)))

include hc hn in
theorem pairing (j : I) :
    (∫ h, character S a h⁻¹ * (S j).character h ∂TauCeti.haarProb H) = (a j : ℂ) := by
  classical
  simp only [character, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun i _ =>
    (CompactHomDimension.integrable_character_mul (S i) (S j) (hc i) (hc j)).const_mul _)]
  simp_rw [integral_const_mul, CompactHomDimension.integral_character_mul_eq_finrank
    _ _ (hc _) (hc j)]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    let : IsEmpty (Representation.Equiv (S i) (S j)) := hn i j hij
    simp [Module.finrank_zero_of_subsingleton]
  · simp

include hc hn in
theorem character_injective : Function.Injective (character S) := by
  intro a b hab
  funext i
  have ha := pairing S a hc hn i
  have hb := pairing S b hc hn i
  rw [hab] at ha
  exact_mod_cast ha.symm.trans hb

variable {L N : Type*}
  [NormedAddCommGroup L] [NormedSpace ℂ L] [FiniteDimensional ℂ L]
  [NormedAddCommGroup N] [NormedSpace ℂ N] [FiniteDimensional ℂ N]

include hc hn in
theorem nonnegative_of_actual (rho : Representation ℂ H L)
    (hr : IsJointlyContinuous rho)
    (he : ∀ h, rho.character h = character S a h) (j : I) : 0 ≤ a j := by
  have hm : (Module.finrank ℂ (IntertwiningMap rho (S j)) : ℂ) = (a j : ℂ) := by
    rw [← CompactHomDimension.integral_character_mul_eq_finrank rho (S j) hr (hc j)]
    simp_rw [he]
    exact pairing S a hc hn j
  have hm' : (Module.finrank ℂ (IntertwiningMap rho (S j)) : ℤ) = a j := by exact_mod_cast hm
  rw [← hm']
  exact Int.natCast_nonneg _

include hc hn in
theorem hom_difference (rho : Representation ℂ H L) (sigma : Representation ℂ H N)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (he : ∀ h, rho.character h - sigma.character h = character S a h) (j : I) :
    (Module.finrank ℂ (IntertwiningMap rho (S j)) : ℤ) -
      (Module.finrank ℂ (IntertwiningMap sigma (S j)) : ℤ) = a j := by
  have heq : (Module.finrank ℂ (IntertwiningMap rho (S j)) : ℂ) -
      (Module.finrank ℂ (IntertwiningMap sigma (S j)) : ℂ) = (a j : ℂ) := by
    rw [← CompactHomDimension.integral_character_mul_eq_finrank rho (S j) hr (hc j),
      ← CompactHomDimension.integral_character_mul_eq_finrank sigma (S j) hs (hc j),
      ← integral_sub
        (CompactHomDimension.integrable_character_mul rho (S j) hr (hc j))
        (CompactHomDimension.integrable_character_mul sigma (S j) hs (hc j))]
    simp_rw [← sub_mul, he]
    exact pairing S a hc hn j
  exact_mod_cast heq

include hc hn in
theorem exists_split (rho : Representation ℂ H L) (sigma : Representation ℂ H N)
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (he : ∀ h, rho.character h - sigma.character h = character S a h)
    (j : I) (hj : 0 < a j) : Nonempty (Split rho (S j)) := by
  have hm := hom_difference S a hc hn rho sigma hr hs he j
  have hp : 0 < Module.finrank ℂ (IntertwiningMap rho (S j)) := by omega
  let : Nontrivial (IntertwiningMap rho (S j)) := Module.finrank_pos_iff.mp hp
  obtain ⟨p, hp⟩ := exists_ne (0 : IntertwiningMap rho (S j))
  have hsurj := (IsIrreducible.surjective_or_eq_zero p).resolve_right hp
  obtain ⟨split, _⟩ := SemisimpleSplitting.exists_split rho (S j)
    (CompactIrreducibleQuotient.semisimple rho hr) p hsurj
  exact ⟨split⟩

end
end Math.CompactVirtualCharacter
