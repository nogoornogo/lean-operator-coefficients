import Math.RepresentationTheory.Characters.UnitaryCharacterSpectrum

/-! Restriction of actual unitary spectra. Under a surjective homomorphism,
distinct characters remain distinct and each full multiplicity is preserved. -/

set_option autoImplicit false

namespace Math.UnitaryCharacterSpectrum

noncomputable section

open AbelianActualSpectrum

variable {G K E : Type*} [CommGroup G] [CommGroup K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ G E) (hu : UnitaryMultiplicity.IsUnitaryRepresentation rho)
  (f : K →* G)

omit [FiniteDimensional ℂ E] in
include hu in
theorem comp_unitary : UnitaryMultiplicity.IsUnitaryRepresentation (rho.comp f) :=
  fun k x y => hu (f k) x y

theorem spectrum_comp :
    spectrum (rho.comp f) (comp_unitary rho hu f) =
      Finsupp.mapDomain (fun chi : G →* ℂ => chi.comp f) (spectrum rho hu) := by
  apply eval_injective
  intro k
  rw [spectrum_eval]
  change rho.character (f k) = _
  rw [← spectrum_eval rho hu (f k)]
  unfold eval
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · simp
  · intros; simp [add_mul]

theorem spectrum_comp_apply (hf : Function.Surjective f) (chi : G →* ℂ) :
    spectrum (rho.comp f) (comp_unitary rho hu f) (chi.comp f) = spectrum rho hu chi := by
  rw [spectrum_comp rho hu f]
  apply Finsupp.mapDomain_apply_of_injective
  intro a b he
  ext g
  obtain ⟨k, rfl⟩ := hf g
  exact congrArg (fun c : K →* ℂ => c k) he

end

end Math.UnitaryCharacterSpectrum
