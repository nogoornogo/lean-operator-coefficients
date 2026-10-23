import Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex
import Math.RepresentationTheory.Characters.UnitaryCharacterSpectrum

open Math

/-!
# Coefficient-level mass conservation and actual zero modes

The finite-character model is faithful, so the algebraic dual character
identity becomes coefficient-level conservation. Positive oriented target
coefficients force actual vectors in the radical. Arbitrary Abelian groups,
including finite groups and self-dual characters, are allowed.
-/

set_option autoImplicit false

namespace Physics.AbelianMassSpectrum

noncomputable section

open Physics.InvariantWeylMass AbelianActualSpectrum UnitaryCharacterSpectrum

variable {H E : Type*} [CommGroup H] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {rho : Representation ℂ H E} (B : SymmetricMass rho)
  (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)

omit [FiniteDimensional ℂ E] in
include hu in
theorem radical_unitary : UnitaryMultiplicity.IsUnitaryRepresentation
    B.radical.toRepresentation := fun h v w => hu h v w

def radicalSpectrum : Polynomial H :=
  spectrum B.radical.toRepresentation (radical_unitary B hu)

theorem radicalSpectrum_nonneg (chi : H →* ℂ) : 0 ≤ radicalSpectrum B hu chi :=
  spectrum_nonneg _ _ chi

@[simp] theorem radicalSpectrum_eval (h : H) :
    eval (radicalSpectrum B hu) h = B.radical.toRepresentation.character h :=
  spectrum_eval _ _ h

/-- Massive self-dual pairs cancel at each character, not only after summing. -/
theorem radical_dual_spectrum_eq :
    radicalSpectrum B hu - dual (radicalSpectrum B hu) =
      spectrum rho hu - dual (spectrum rho hu) := by
  apply eval_injective
  intro h
  simp only [eval_sub, eval_dual, radicalSpectrum_eval, spectrum_eval]
  simpa only [Representation.char_dual] using B.radical_dual_character_eq h

/-- A source-character target identifies the radical's dual coefficients. -/
theorem radical_dual_spectrum_eq_target (p : Polynomial H)
    (ht : ∀ h, rho.character h - rho.dual.character h = eval p h) :
    radicalSpectrum B hu - dual (radicalSpectrum B hu) = p := by
  rw [radical_dual_spectrum_eq]
  apply eval_injective
  intro h
  simpa only [eval_sub, eval_dual, spectrum_eval, Representation.char_dual] using ht h

/-- A light dual-character target is sufficient for the same source input. -/
theorem source_target_of_radical_target (p : Polynomial H)
    (ht : ∀ h, B.radical.toRepresentation.character h -
      B.radical.toRepresentation.dual.character h = eval p h) :
    ∀ h, rho.character h - rho.dual.character h = eval p h := by
  intro h
  exact (B.radical_dual_character_eq h).symm.trans (ht h)

theorem coefficient_lower_bound (p : Polynomial H)
    (ht : ∀ h, rho.character h - rho.dual.character h = eval p h)
    (chi : H →* ℂ) : p chi ≤ radicalSpectrum B hu chi := by
  have he := congrArg (fun q : Polynomial H => q chi)
    (radical_dual_spectrum_eq_target B hu p ht)
  have hn := radicalSpectrum_nonneg B hu (dualCharacter chi)
  simp only [Finsupp.sub_apply, dual_apply] at he
  omega

include hu in
theorem exists_radical_vector_of_pos (p : Polynomial H)
    (ht : ∀ h, rho.character h - rho.dual.character h = eval p h)
    (chi : H →* ℂ) (hp : 0 < p chi) :
    ∃ v : B.radical.toSubmodule, v ≠ 0 ∧
      ∀ h, B.radical.toRepresentation h v = chi h • v := by
  apply exists_eigenvector_of_coeff_ne_zero B.radical.toRepresentation (radical_unitary B hu)
  have := coefficient_lower_bound B hu p ht chi
  change radicalSpectrum B hu chi ≠ 0
  omega

include hu in
/-- Ambient-field version records both zero mass and the exact character. -/
theorem exists_zeroMode_of_pos (p : Polynomial H)
    (ht : ∀ h, rho.character h - rho.dual.character h = eval p h)
    (chi : H →* ℂ) (hp : 0 < p chi) :
    ∃ v : E, v ≠ 0 ∧ (∀ w, B.form v w = 0) ∧ ∀ h, rho h v = chi h • v := by
  obtain ⟨v, hv, he⟩ := exists_radical_vector_of_pos B hu p ht chi hp
  refine ⟨v, fun hz => hv (Subtype.ext hz), (B.mem_radical v).mp v.property, ?_⟩
  intro h
  exact congrArg Subtype.val (he h)

end

end Physics.AbelianMassSpectrum
