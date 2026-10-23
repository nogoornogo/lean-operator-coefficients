import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraNormalizationClosure
import Mathlib.Analysis.Real.Pi.Bounds

namespace Physics.DevMohapatraMagnitudeObstruction
set_option autoImplicit false
noncomputable section
open DevMohapatraNormalizationClosure DevMohapatraCoefficientReevaluation
open DevMohapatraTreeLevel DevMohapatraLiteratureConvention DevMohapatraHeavyProjection

theorem matching_norm (mu nu a b t : ℂ)
    (h : -(8*(Real.pi : ℂ)^2)*(a*b)^2 = t*mu^2*nu) :
    8*Real.pi^2*(‖a‖*‖b‖)^2 = ‖t‖*‖mu‖^2*‖nu‖ := by
  have hn := congrArg norm h
  have h8 : ‖(8 : ℂ)‖ = (8 : ℝ) := by norm_num
  simpa only [norm_mul, norm_neg, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, h8] using hn

/-- A bounded magnitude compensation cannot supply the missing pi factor. -/
theorem bounded_no_match (mu nu a b t : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hbound : ‖t‖*‖mu‖^2*‖nu‖ ≤ 32*(‖a‖*‖b‖)^2) :
    -(8*(Real.pi : ℂ)^2)*(a*b)^2 ≠ t*mu^2*nu := by
  intro h
  have hn := matching_norm mu nu a b t h
  have hp : 0 < (‖a‖*‖b‖)^2 := sq_pos_of_pos (mul_pos (norm_pos_iff.mpr ha) (norm_pos_iff.mpr hb))
  have hpi := Real.pi_gt_three
  have hs : 32 < 8*Real.pi^2 := by nlinarith
  have ht := mul_lt_mul_of_pos_right hs hp
  linarith

/-- Arbitrary phases include sign flips; no choice of their angles can match. -/
theorem unit_phase_no_match (mu nu a b t : ℂ)
    (hmu : ‖mu‖ = 1) (hnu : ‖nu‖ = 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (ht : ‖t‖ = 1) :
    -(8*(Real.pi : ℂ)^2)*(a*b)^2 ≠ t*mu^2*nu := by
  apply bounded_no_match mu nu a b t
  · intro h; simp [h] at ha
  · intro h; simp [h] at hb
  · norm_num [hmu, hnu, ha, hb, ht]

theorem bounded_action_ne (m M lam z mu nu a b t : ℂ)
    (hm : m ≠ 0) (hM : M ≠ 0) (hl : lam ≠ 0) (hz : z ≠ 0)
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hbound : ‖t‖*‖mu‖^2*‖nu‖ ≤ 32*(‖a‖*‖b‖)^2) :
    projectedAction (mu*m) (nu*M) (a*lam) (b*z) ≠
      paperPrefactor m M lam z • (t • operator ul dl sl) := by
  intro h
  exact bounded_no_match mu nu a b t ha hb hbound
    ((normalization_match_iff m M lam z mu nu a b t hm hM hl hz hmu hnu).mp h)

end
end Physics.DevMohapatraMagnitudeObstruction
