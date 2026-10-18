import GUT.PatiSalam.Matching.ActionTranslation

/-! Independent sum-of-squared-entry check of the canonical source reading.
No universal source-field identification or spectral calculation is asserted. -/
namespace GUT.PatiSalam.MassNormCrosscheck
set_option autoImplicit false
noncomputable section

def weight (a : Matrix (Fin 3) (Fin 3) ℂ) : ℝ := ∑ i, ∑ j, ‖a i j‖^2

theorem weight_mass (d M : ℂ) : weight (NeutralMass.mass d M 0) =
    2*‖d‖^2+2*‖M‖^2 := by
  simp [weight,NeutralMass.mass,Fin.sum_univ_succ]
  ring

theorem displayed_weight_difference (p : ActionTranslation.Input) :
    weight (NeutralMass.mass (ActionTranslation.dirac p) (p.yR*(p.vR:ℂ)) 0) -
      weight (NeutralMass.mass (ActionTranslation.dirac p) (ActionTranslation.mixing p) 0) =
        2*‖ActionTranslation.mixing p‖^2 := by
  rw [weight_mass,weight_mass,ActionTranslation.norm_mixing_ratio]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [sq_nonneg ‖ActionTranslation.mixing p‖]

end
end GUT.PatiSalam.MassNormCrosscheck
