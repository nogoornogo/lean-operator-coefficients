import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected

/-! Path-connectedness of a real unit sphere with two antipodal points removed,
via stereographic projection and a punctured real vector space. -/

set_option autoImplicit false

namespace Math.PuncturedSphere

noncomputable section

open Metric Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem stereo_zero (p : sphere (0 : E) 1) :
    (stereographic (norm_eq_of_mem_sphere p)).symm 0 = -p := by
  apply Subtype.ext
  change (stereoInvFun (norm_eq_of_mem_sphere p) 0 : E) = -p.val
  norm_num [stereoInvFun_apply, smul_smul]

omit [FiniteDimensional ℝ E] in
theorem stereo_image_compl_zero (p : sphere (0 : E) 1) :
    (stereographic (norm_eq_of_mem_sphere p)).symm '' ({0}ᶜ) =
      ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) := by
  rw [Set.image_compl_eq_range_sdiff_image
    (isOpenEmbedding_stereographic_symm (norm_eq_of_mem_sphere p)).injective]
  rw [range_stereographic_symm (norm_eq_of_mem_sphere p) p.property,
    Set.image_singleton, stereo_zero]
  rfl

theorem isPathConnected_compl_antipodes (hE : 2 < finrank ℝ E)
    (p : sphere (0 : E) 1) : IsPathConnected ({p}ᶜ ∩ {-p}ᶜ : Set (sphere (0 : E) 1)) := by
  have hp : p.val ≠ 0 := by
    intro hp
    have hn := norm_eq_of_mem_sphere p
    rw [hp, norm_zero] at hn
    norm_num at hn
  have hd := (ℝ ∙ p.val).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hp] at hd
  have hdim : 1 < Module.rank ℝ ((ℝ ∙ p.val)ᗮ) := by
    rw [← finrank_eq_rank]
    exact_mod_cast (show 1 < finrank ℝ ((ℝ ∙ p.val)ᗮ) by omega)
  rw [← stereo_image_compl_zero]
  exact (isPathConnected_compl_singleton_of_one_lt_rank hdim 0).image
    (continuous_stereoInvFun (norm_eq_of_mem_sphere p))

end

end Math.PuncturedSphere
