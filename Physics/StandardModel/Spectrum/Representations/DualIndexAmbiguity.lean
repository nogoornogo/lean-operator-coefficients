import Physics.StandardModel.Spectrum.Representations.HyperchargeReversalProbe
import Math.RepresentationTheory.Constructions.DualIndexCompatibility

/-! Actual SM gauge spectra with equal dual indices but different charged
content. This does not construct a UV SU(6) mass or vacuum model. -/
namespace Physics.SMDualIndexAmbiguity
set_option autoImplicit false
noncomputable section
open Representation

/-- One SM generation plus an SM generation and its dual. -/
abbrev enlargedGeneration := Math.DualIndexCompatibility.withVectorlike ExactSMSpectrum.generation

theorem equal_dual_index (g : StandardSMGaugeTensor.GaugeGroup) :
    enlargedGeneration.character g - enlargedGeneration.dual.character g =
      ExactSMSpectrum.generation.character g - ExactSMSpectrum.generation.dual.character g :=
  Math.DualIndexCompatibility.withVectorlike_dual_index _ g

theorem generation_character_one : ExactSMSpectrum.generation.character 1 = 15 := by
  simp

theorem enlarged_character_one : enlargedGeneration.character 1 = 45 := by
  simp only [enlargedGeneration, Math.DualIndexCompatibility.withVectorlike,
    char_prod, char_dual, inv_one]
  norm_num

/-- A positive one-generation dual index does not determine the full charged
SM representation: the exhibited pair has the same index and dimension 45. -/
theorem not_equiv : ¬ Nonempty (Representation.Equiv ExactSMSpectrum.generation
    enlargedGeneration) := by
  rintro ⟨e⟩
  have he := congrFun (char_iso e) 1
  rw [generation_character_one, enlarged_character_one] at he
  norm_num at he
end
end Physics.SMDualIndexAmbiguity
