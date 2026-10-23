import GUT.PatiSalam.Matching.SourceConnection
import Physics.FieldTheory.Mass.Spectrum.ChiralActionConvention

open Physics

/-! A single canonical chiral convention for the displayed Yukawa action.
Real chosen scalar VEVs, complex source couplings, and explicit Hermitian
conjugation. No full PS branching or finite-mu spectrum is inferred. -/
namespace GUT.PatiSalam.ActionTranslation
set_option autoImplicit false
noncomputable section

structure Input where
  CL : ℂ
  CR : ℂ
  vR : ℝ
  w : ℝ
  Lambda : ℂ
  yR : ℂ
  yPhi : ℂ
  m : ℂ

def componentVEV (p : Input) : ℂ := ((p.vR / Real.sqrt 2 : ℝ) : ℂ)
def dirac (p : Input) : ℂ := -(star p.yPhi) * (p.w : ℂ)
def mixing (p : Input) : ℂ := star p.yR * componentVEV p

/-- Source Eq.(6) has a plus Yukawa sign; standard mass action has a minus.
The source Eq.(10) has a minus sign. Conjugation therefore matters in both. -/
def parameters (p : Input) : ModelApplication.Parameters :=
  ⟨p.CL,p.CR,componentVEV p,p.Lambda,p.yR,-star p.yPhi,mixing p,p.m,(p.w : ℂ)⟩

theorem parameters_dirac (p : Input) :
    (parameters p).Y*star (parameters p).w = dirac p := by
  simp [parameters, dirac]

/-- A single translated holomorphic action; the colored vertex still uses
source yR in its anti-holomorphic term, not the mass coefficient star(yR). -/
def massAction (p : Input) : Physics.WeylGrassmannAction.Algebra (Fin 3) :=
  -(dirac p • Physics.WeylGrassmannAction.pair 0 1 +
    mixing p • Physics.WeylGrassmannAction.pair 1 2)

theorem action_matrix (p : Input) : massAction p = Physics.WeylGrassmannAction.action
    (NeutralMass.mass ((parameters p).Y*star (parameters p).w) (parameters p).M 0) := by
  rw [parameters_dirac]
  unfold NeutralMass.mass
  rw [Physics.WeylGrassmannAction.three_species_action]
  simp [massAction, parameters]

variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

/-- The same source coupling is translated for every chi component, including
neutral mass and colored vertex, without separate coupling redefinitions. -/
theorem translated_chi_vertex (p : Input) (z : ℂ) (s n : Fin 2 → R)
    (h0 : star (s 0)*star (n 1) = -(star (n 1)*star (s 0)))
    (h1 : star (s 1)*star (n 0) = -(star (n 0)*star (s 1))) :
    star ((-(p.yR*star z)) • Physics.ChiralActionConvention.barredLR s n) =
      (-(star p.yR*z)) • Physics.ChiralActionConvention.bracket s n :=
  Physics.ChiralActionConvention.conjugate_vertex p.yR z s n h0 h1

theorem translated_majorana_vertex (p : Input) (z : ℂ) (s n : Fin 2 → R)
    (h0 : star (s 0)*star (n 1) = -(star (n 1)*star (s 0)))
    (h1 : star (s 1)*star (n 0) = -(star (n 0)*star (s 1))) :
    star ((-(p.yR*star z)) • Physics.ChiralActionConvention.majoranaBarRight s n) =
      (-(star p.yR*z)) • Physics.ChiralActionConvention.bracket s n := by
  rw [Physics.ChiralActionConvention.majorana_bar_right]
  exact translated_chi_vertex p z s n h0 h1

theorem translated_neutral (p : Input) (s n : Fin 2 → R)
    (h0 : star (s 0)*star (n 1) = -(star (n 1)*star (s 0)))
    (h1 : star (s 1)*star (n 0) = -(star (n 0)*star (s 1))) :
    star ((-(p.yR*star (componentVEV p))) • Physics.ChiralActionConvention.barredLR s n) =
      (-mixing p) • Physics.ChiralActionConvention.bracket s n :=
  translated_chi_vertex p _ s n h0 h1

theorem translated_phi (p : Input) (s n : Fin 2 → R)
    (h0 : star (s 0)*star (n 1) = -(star (n 1)*star (s 0)))
    (h1 : star (s 1)*star (n 0) = -(star (n 0)*star (s 1))) :
    star ((p.yPhi*(p.w : ℂ)) • Physics.ChiralActionConvention.barredLR s n) =
      (-dirac p) • Physics.ChiralActionConvention.bracket s n := by
  rw [Physics.ChiralActionConvention.barred_lr s n h0 h1]
  simp [dirac]

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem sqrt_two_nonzero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num)))

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem component_nonzero (p : Input) (hv : p.vR ≠ 0) : componentVEV p ≠ 0 := by
  unfold componentVEV
  exact_mod_cast div_ne_zero hv (by exact_mod_cast sqrt_two_nonzero)

def lightCoefficient (p : Input) := NormalizedLight.coefficient (parameters p)

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem light_nonzero_iff (p : Input) (hL : p.Lambda ≠ 0) (hm : p.m ≠ 0)
    (hy : p.yR ≠ 0) (hv : p.vR ≠ 0) :
    lightCoefficient p ≠ 0 ↔ p.w ≠ 0 ∧ p.yPhi ≠ 0 ∧ (p.CL ≠ 0 ∨ p.CR ≠ 0) := by
  rw [lightCoefficient, NormalizedLight.nonzero_iff (parameters p) hL hm
    (mul_ne_zero (star_ne_zero.mpr hy) (component_nonzero p hv))]
  simp [parameters, component_nonzero p hv, hy]

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem norm_mixing_ratio (p : Input) :
    ‖p.yR*(p.vR : ℂ)‖ = Real.sqrt 2 * ‖mixing p‖ := by
  simp only [mixing, componentVEV, Complex.ofReal_div, norm_mul, norm_star,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  have hs : Real.sqrt 2 ≠ 0 := by exact_mod_cast sqrt_two_nonzero
  field_simp

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem displayed_mixing_norm_mismatch (p : Input) (hy : p.yR ≠ 0) (hv : p.vR ≠ 0) :
    ‖mixing p‖ ≠ ‖p.yR*(p.vR : ℂ)‖ := by
  intro h
  have hn : ‖mixing p‖ ≠ 0 := norm_ne_zero_iff.mpr
    (mul_ne_zero (star_ne_zero.mpr hy) (component_nonzero p hv))
  have he := norm_mixing_ratio p
  rw [← h] at he
  have hr : Real.sqrt 2 = 1 := (mul_right_cancel₀ hn) (by simpa using he.symm)
  exact SourceConnection.sqrt_two_ne_one (by exact_mod_cast hr)

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem normalized_kernel (p : Input) (hy : p.yR ≠ 0) (hv : p.vR ≠ 0) :
    NormalizedLight.massMap (dirac p) (mixing p)
      (NormalizedLight.unitMode (dirac p) (mixing p)) = 0 :=
  NormalizedLight.unit_kernel _ _
    (mul_ne_zero (star_ne_zero.mpr hy) (component_nonzero p hv))

omit [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem zero_uv (p : Input) (hL : p.CL = 0) (hR : p.CR = 0) :
    lightCoefficient p = 0 := NormalizedLight.zero_uv (parameters p) hL hR

end
end GUT.PatiSalam.ActionTranslation
