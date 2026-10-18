import Math.RepresentationTheory.Characters.CompactHomDimension

/-! Positive actual character content yields an irreducible quotient for
compact continuous representations. No classification of irreducibles is used. -/

namespace Math.CompactPositiveCharacterQuotient
noncomputable section

open Representation ContinuousRepresentationScope

variable {H L S R U : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup L] [NormedSpace ℂ L] [FiniteDimensional ℂ L]
  [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup R] [NormedSpace ℂ R] [FiniteDimensional ℂ R]
  [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℂ U]

theorem exists_surjective_of_character_add_of_nonzero
    (rho : Representation ℂ H L) (sigma : Representation ℂ H S)
    (tau : Representation ℂ H R) (upsilon : Representation ℂ H U)
    [IsIrreducible upsilon]
    (hr : IsJointlyContinuous rho) (hs : IsJointlyContinuous sigma)
    (ht : IsJointlyContinuous tau) (hu : IsJointlyContinuous upsilon)
    (hc : ∀ h, rho.character h = sigma.character h + tau.character h)
    (f : IntertwiningMap tau upsilon) (hf : f ≠ 0) :
    ∃ p : IntertwiningMap rho upsilon, Function.Surjective p := by
  have hd := CompactHomDimension.hom_finrank_add rho sigma tau upsilon hr hs ht hu hc
  have hp : 0 < Module.finrank ℂ (IntertwiningMap tau upsilon) := by
    let : Nontrivial (IntertwiningMap tau upsilon) := nontrivial_of_ne f 0 hf
    exact Module.finrank_pos
  have hl : 0 < Module.finrank ℂ (IntertwiningMap rho upsilon) := by omega
  let : Nontrivial (IntertwiningMap rho upsilon) := Module.finrank_pos_iff.mp hl
  obtain ⟨p, hp⟩ := exists_ne (0 : IntertwiningMap rho upsilon)
  exact ⟨p, (IsIrreducible.surjective_or_eq_zero p).resolve_right hp⟩

end
end Math.CompactPositiveCharacterQuotient
