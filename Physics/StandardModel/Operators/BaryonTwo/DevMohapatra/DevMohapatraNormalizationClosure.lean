import Physics.StandardModel.Operators.BaryonTwo.DevMohapatra.DevMohapatraCoefficientReevaluation

namespace Physics.DevMohapatraNormalizationClosure
set_option autoImplicit false
noncomputable section
open DevMohapatraTreeLevel DevMohapatraHeavyProjection
open DevMohapatraLiteratureConvention DevMohapatraCoefficientReevaluation

def coordinates : Light →ₗ[ℂ] Coordinates where
  toFun x i := x ⟨6*i.1.val+2*i.2.1.val+i.2.2.val, by omega⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coordinates_fields (c : Fin 3) (r : Fin 2) :
    coordinates (ul c r) = field 0 c r ∧
    coordinates (dl c r) = field 1 c r ∧
    coordinates (sl c r) = field 2 c r := by
  constructor
  · ext i
    rcases i with ⟨s,c',r'⟩
    fin_cases s <;> fin_cases c <;> fin_cases r <;> fin_cases c' <;> fin_cases r' <;>
      simp [coordinates, ul, holomorphicFields, DevMohapatraHeavyElimination.u,
        DevMohapatraHeavyElimination.coord, field, Pi.basisFun_apply, Pi.single_apply]
  · constructor
    · ext i
      rcases i with ⟨s,c',r'⟩
      fin_cases s <;> fin_cases c <;> fin_cases r <;> fin_cases c' <;> fin_cases r' <;>
        simp [coordinates, dl, holomorphicFields, DevMohapatraHeavyElimination.d,
          DevMohapatraHeavyElimination.coord, field, Pi.basisFun_apply, Pi.single_apply]
    · ext i
      rcases i with ⟨s,c',r'⟩
      fin_cases s <;> fin_cases c <;> fin_cases r <;> fin_cases c' <;> fin_cases r' <;>
        simp [coordinates, sl, holomorphicFields, DevMohapatraHeavyElimination.s,
          DevMohapatraHeavyElimination.coord, field, Pi.basisFun_apply, Pi.single_apply]

theorem operator_nonzero : operator ul dl sl ≠ 0 := by
  intro h
  have hp : printedOperator ul dl sl = 0 := by
    simpa [operator_transport, DevMohapatraSignedConvention.inverseOperator_eq] using h
  have hg : generated 1 1 1 1 ul dl sl = 0 := by rw [generated_printed, hp, smul_zero]
  have hm := congrArg (ExteriorAlgebra.map coordinates) hg
  simp only [generated, map_smul, map_mul, map_current,
    (coordinates_fields _ _).1, (coordinates_fields _ _).2.1,
    (coordinates_fields _ _).2.2, map_zero] at hm
  exact generated_nonzero 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hm

theorem paper_nonzero (m M lam z : ℂ) (hm : m ≠ 0) (hM : M ≠ 0)
    (hl : lam ≠ 0) (hz : z ≠ 0) : paperPrefactor m M lam z ≠ 0 := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact div_ne_zero (pow_ne_zero 2 (mul_ne_zero hl hz))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp))
      (pow_ne_zero 2 hm)) hM)

theorem action_ne_paper (m M lam z : ℂ) (hm : m ≠ 0) (hM : M ≠ 0)
    (hl : lam ≠ 0) (hz : z ≠ 0) :
    projectedAction m M lam z ≠ paperPrefactor m M lam z • operator ul dl sl := by
  intro h
  rw [independent_comparison m M lam z hm hM] at h
  have he := smul_left_injective ℂ operator_nonzero h
  have hf : -(8 * (Real.pi : ℂ)^2) = 1 :=
    (mul_eq_right₀ (paper_nonzero m M lam z hm hM hl hz)).mp he
  have hr : -(8 * Real.pi^2) = (1 : ℝ) := by exact_mod_cast hf
  nlinarith [sq_nonneg Real.pi]

theorem ordered_action_ne_paper (m M lam z : ℂ) (hm : m ≠ 0) (hM : M ≠ 0)
    (hl : lam ≠ 0) (hz : z ≠ 0) :
    projectedAction m M lam (2*z) ≠ paperPrefactor m M lam z • operator ul dl sl := by
  intro h
  rw [ordered_comparison m M lam z hm hM] at h
  have he := smul_left_injective ℂ operator_nonzero h
  have hf : -(32 * (Real.pi : ℂ)^2) = 1 :=
    (mul_eq_right₀ (paper_nonzero m M lam z hm hM hl hz)).mp he
  have hr : -(32 * Real.pi^2) = (1 : ℝ) := by exact_mod_cast hf
  nlinarith [sq_nonneg Real.pi]

/-- Supplied component identifications; not an automatic field redefinition. -/
theorem normalization_coefficient (m M lam z mu nu a b : ℂ)
    (hm : m ≠ 0) (hM : M ≠ 0) (hmu : mu ≠ 0) (hnu : nu ≠ 0) :
    coefficient (mu*m) (nu*M) (a*lam) (b*z) =
      (-(8*(Real.pi : ℂ)^2)*(a*b)^2/(mu^2*nu)) * paperPrefactor m M lam z := by
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold coefficient treePrefactor paperPrefactor
  field_simp [hm, hM, hmu, hnu, hp]
  ring

theorem normalization_match_iff (m M lam z mu nu a b t : ℂ)
    (hm : m ≠ 0) (hM : M ≠ 0) (hl : lam ≠ 0) (hz : z ≠ 0)
    (hmu : mu ≠ 0) (hnu : nu ≠ 0) :
    projectedAction (mu*m) (nu*M) (a*lam) (b*z) =
      paperPrefactor m M lam z • (t • operator ul dl sl) ↔
      -(8*(Real.pi : ℂ)^2)*(a*b)^2 = t*mu^2*nu := by
  rw [projectedAction_coefficient _ _ _ _ (mul_ne_zero hnu hM), smul_smul]
  have hinj := (smul_left_injective ℂ operator_nonzero).eq_iff
    (a := coefficient (mu*m) (nu*M) (a*lam) (b*z))
    (b := paperPrefactor m M lam z * t)
  rw [hinj, normalization_coefficient m M lam z mu nu a b hm hM hmu hnu]
  have hp := paper_nonzero m M lam z hm hM hl hz
  have hcancel (x y : ℂ) :
      x * paperPrefactor m M lam z = y * paperPrefactor m M lam z ↔ x = y :=
    ⟨mul_right_cancel₀ hp, fun h => congrArg (fun q => q * paperPrefactor m M lam z) h⟩
  rw [mul_comm (paperPrefactor m M lam z) t, hcancel]
  rw [div_eq_iff (mul_ne_zero (pow_ne_zero 2 hmu) hnu)]
  simp only [mul_assoc]

/-- A common bilinear change scales both compared coefficients by c cubed. -/
theorem consistent_bilinear_match_iff (m M lam z c : ℂ)
    (hM : M ≠ 0) (hc : c ≠ 0) :
    coefficient m (c*M) (c*lam) (c*z) =
      c^3 * paperPrefactor m M lam z ↔
      coefficient m M lam z = paperPrefactor m M lam z := by
  have hs := DevMohapatraSignedConvention.consistent_bilinear_rescaling
    m M lam z c hc hM
  simp only [coefficient, hs, ← mul_neg]
  exact ⟨mul_left_cancel₀ (pow_ne_zero 3 hc),
    fun h => congrArg (fun q : ℂ => c^3 * q) h⟩

end
end Physics.DevMohapatraNormalizationClosure
