import GUT.PatiSalam.Matching.ActionTranslation

/-! Exact mu=0 comparison within the fixed canonical source dictionary. -/
namespace GUT.PatiSalam.DisplayedKernelComparison
set_option autoImplicit false
noncomputable section

theorem mode_kernel_iff (d M K : ℂ) (hd : d ≠ 0) (hK : K ≠ 0) :
    (NeutralMass.mass d M 0).mulVec (NeutralMass.mode d K) = 0 ↔ M=K := by
  constructor
  · intro h
    have he := congrFun h 1
    simp [NeutralMass.mass,NeutralMass.mode,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] at he
    have he' : (K-M)*d = 0 := by
      field_simp at he
      linear_combination he
    exact (sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hd)).symm
  · intro h
    subst M
    exact NeutralMass.exact_zero_mode d K hK

/-- A nonzero common action factor preserves the exact kernel test.
This does not cover independent changes of field normalization. -/
theorem common_scale_mode_kernel_iff (c d M K : ℂ) (hc : c ≠ 0)
    (hd : d ≠ 0) (hK : K ≠ 0) :
    (c • NeutralMass.mass d M 0).mulVec (NeutralMass.mode d K) = 0 ↔ M = K := by
  rw [Matrix.smul_mulVec]
  constructor
  · intro h
    have hz : (NeutralMass.mass d M 0).mulVec (NeutralMass.mode d K) = 0 :=
      (smul_eq_zero.mp h).resolve_left hc
    exact (mode_kernel_iff d M K hd hK).mp hz
  · intro h
    rw [(mode_kernel_iff d M K hd hK).mpr h, smul_zero]

theorem displayed_mode_not_kernel (p : ActionTranslation.Input)
    (hy : p.yR ≠ 0) (hv : p.vR ≠ 0) (hd : ActionTranslation.dirac p ≠ 0) :
    (NeutralMass.mass (ActionTranslation.dirac p) (ActionTranslation.mixing p) 0).mulVec
      (NeutralMass.mode (ActionTranslation.dirac p) (p.yR*(p.vR:ℂ))) ≠ 0 := by
  intro h
  have hK : p.yR*(p.vR:ℂ) ≠ 0 := mul_ne_zero hy (by exact_mod_cast hv)
  have he := (mode_kernel_iff _ _ _ hd hK).mp h
  exact ActionTranslation.displayed_mixing_norm_mismatch p hy hv (congrArg norm he)

theorem displayed_common_scale_not_kernel (p : ActionTranslation.Input)
    (c : ℂ) (hc : c ≠ 0) (hy : p.yR ≠ 0) (hv : p.vR ≠ 0)
    (hd : ActionTranslation.dirac p ≠ 0) :
    (c • NeutralMass.mass (ActionTranslation.dirac p) (ActionTranslation.mixing p) 0).mulVec
      (NeutralMass.mode (ActionTranslation.dirac p) (p.yR*(p.vR:ℂ))) ≠ 0 := by
  rw [Matrix.smul_mulVec]
  exact smul_ne_zero hc (displayed_mode_not_kernel p hy hv hd)

theorem displayed_normalized_not_kernel (p : ActionTranslation.Input)
    (hy : p.yR ≠ 0) (hv : p.vR ≠ 0) (hd : ActionTranslation.dirac p ≠ 0) :
    (NeutralMass.mass (ActionTranslation.dirac p) (ActionTranslation.mixing p) 0).mulVec
      (fun i => NormalizedLight.unitMode (ActionTranslation.dirac p) (p.yR*(p.vR:ℂ)) i) ≠ 0 := by
  have he : (fun i => NormalizedLight.unitMode (ActionTranslation.dirac p) (p.yR*(p.vR:ℂ)) i) =
      NormalizedLight.scale (ActionTranslation.dirac p) (p.yR*(p.vR:ℂ)) •
        NeutralMass.mode (ActionTranslation.dirac p) (p.yR*(p.vR:ℂ)) := by
    funext i
    exact NormalizedLight.unit_coordinate _ _ i
  rw [he,Matrix.mulVec_smul]
  exact smul_ne_zero (NormalizedLight.scale_nonzero _ _) (displayed_mode_not_kernel p hy hv hd)

/-- Coefficient in new barred coordinates xi'=a xi, fR'=b fR, chi'=h chi. -/
def rescaledYukawa (y a b h : ℂ) : ℂ := y / (star a * star h * b)

/-- Direct substitution of all three fields recovers the old monomial. -/
theorem rescaled_vertex (y a b h x z r : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    rescaledYukawa y a b h * star (a*x) * star (h*z) * (b*r) =
      y * star x * star z * r := by
  simp only [rescaledYukawa, star_mul]
  have ha' := star_ne_zero.mpr ha
  have hh' := star_ne_zero.mpr hh
  field_simp

/-- Neutral mixing and the colored vertex transform using the same coupling. -/
theorem rescaled_mixing (y v a b h : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    rescaledYukawa y a b h * star (h*v) =
      (y * star v) / (star a * b) := by
  simp only [rescaledYukawa, star_mul]
  have ha' := star_ne_zero.mpr ha
  have hh' := star_ne_zero.mpr hh
  field_simp

/-- The VEV definition is imposed in the new coordinates too. No kinetic
metric or completeness of possible PS convention changes is asserted. -/
theorem rescaled_norm_discrepancy (y v a b h : ℂ)
    (hy : y ≠ 0) (hv : v ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    norm (rescaledYukawa y a b h * ((Real.sqrt 2 : ℂ) * (h*v))) ≠
      norm (rescaledYukawa y a b h * star (h*v)) := by
  have hn : rescaledYukawa y a b h ≠ 0 := by
    exact div_ne_zero hy (mul_ne_zero (mul_ne_zero (star_ne_zero.mpr ha)
      (star_ne_zero.mpr hh)) hb)
  have hp : norm (rescaledYukawa y a b h) * norm (h*v) ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hn) (norm_ne_zero_iff.mpr (mul_ne_zero hh hv))
  have hs : norm (Real.sqrt 2 : ℂ) ≠ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    intro he
    have he2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
    rw [he] at he2
    norm_num at he2
  simp only [norm_mul, norm_star]
  intro he
  have he' : (norm (Real.sqrt 2 : ℂ) - 1) *
      (norm (rescaledYukawa y a b h) * norm (h*v)) = 0 := by
    simp only [norm_mul]
    nlinarith [he]
  exact hs (sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hp))

end
end GUT.PatiSalam.DisplayedKernelComparison
