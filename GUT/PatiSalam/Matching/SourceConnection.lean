import GUT.PatiSalam.Matching.ComponentAdmission
import GUT.PatiSalam.Matching.NormalizedLight
import Physics.FieldTheory.Mass.Algebra.WeylGrassmannAction

open Physics

/-! Literal selected component action to normalized light coefficient, and a
restricted source-convention compatibility test. No full PS or four-component
charge-conjugation adapter is asserted. -/
namespace GUT.PatiSalam.SourceConnection
set_option autoImplicit false
noncomputable section

structure Input where
  CL : ℂ
  CR : ℂ
  v : ℂ
  Lambda : ℂ
  y : ℂ
  Y : ℂ
  m : ℂ
  w : ℂ

def dirac (p : Input) := ComponentAdmission.diracEntry p.Y 0 (star p.w) 0 0
def mixing (p : Input) := p.y * star p.v

theorem dirac_eq (p : Input) : dirac p = p.Y*star p.w := by
  simp [dirac, ComponentAdmission.diracEntry, ComponentAdmission.phiVEV,
    ComponentAdmission.conjugatePhiVEV]

theorem vertex_to_mixing (p : Input) (f : ComponentAdmission.Array) :
    -p.y * ComponentAdmission.contraction (ComponentAdmission.neutralVEV p.v) f =
      -mixing p * f 3 0 := ComponentAdmission.yukawa_neutral _ _ _

def sourceAction (p : Input) : Physics.WeylGrassmannAction.Algebra (Fin 3) :=
  -(dirac p • Physics.WeylGrassmannAction.pair 0 1 +
    mixing p • Physics.WeylGrassmannAction.pair 1 2)

theorem action_to_matrix (p : Input) :
    sourceAction p = Physics.WeylGrassmannAction.action
      (NeutralMass.mass (dirac p) (mixing p) 0) := by
  unfold NeutralMass.mass
  rw [Physics.WeylGrassmannAction.three_species_action]
  simp [sourceAction]

def parameters (p : Input) : ModelApplication.Parameters :=
  ⟨p.CL,p.CR,p.v,p.Lambda,p.y,p.Y,mixing p,p.m,p.w⟩

theorem action_parameters (p : Input) :
    sourceAction p = Physics.WeylGrassmannAction.action
      (NeutralMass.mass ((parameters p).Y*star (parameters p).w) (parameters p).M 0) := by
  simpa only [parameters, dirac_eq] using action_to_matrix p

theorem normalized_kernel (p : Input) (hy : p.y ≠ 0) (hv : p.v ≠ 0) :
    NormalizedLight.massMap (dirac p) (mixing p)
      (NormalizedLight.unitMode (dirac p) (mixing p)) = 0 :=
  NormalizedLight.unit_kernel _ _ (mul_ne_zero hy (star_ne_zero.mpr hv))

def lightCoefficient (p : Input) := NormalizedLight.coefficient (parameters p)

theorem light_nonzero_iff (p : Input) (hL : p.Lambda ≠ 0) (hm : p.m ≠ 0)
    (hy : p.y ≠ 0) (hv : p.v ≠ 0) :
    lightCoefficient p ≠ 0 ↔ p.w ≠ 0 ∧ p.Y ≠ 0 ∧ (p.CL ≠ 0 ∨ p.CR ≠ 0) := by
  rw [lightCoefficient, NormalizedLight.nonzero_iff (parameters p) hL hm
    (mul_ne_zero hy (star_ne_zero.mpr hv))]
  simp [parameters, hy, hv]

/-- A common overall matrix factor cannot change only the heavy off-diagonal
entry while preserving a nonzero Dirac entry. This is a restricted test, not
an impossibility theorem for all field/coupling redefinitions. -/
theorem common_factor_iff (d M r k : ℂ) (hd : d ≠ 0) (hM : M ≠ 0) :
    k • NeutralMass.mass d M 0 = NeutralMass.mass d (r*M) 0 ↔
      k = 1 ∧ r = 1 := by
  constructor
  · intro h
    have h01 := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℂ => a 0 1) h
    have h12 := congrArg (fun a : Matrix (Fin 3) (Fin 3) ℂ => a 1 2) h
    change k*d = d at h01
    change k*M = r*M at h12
    have hk : k = 1 := (mul_right_cancel₀ hd) (by simpa using h01)
    refine ⟨hk, ?_⟩
    rw [hk] at h12
    exact (mul_right_cancel₀ hM) (by simpa using h12.symm)
  · rintro ⟨rfl,rfl⟩
    simp

theorem sqrt_two_ne_one : (Real.sqrt 2 : ℂ) ≠ 1 := by
  intro h
  have hr : Real.sqrt 2 = 1 := by exact_mod_cast h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  rw [hr] at hs
  norm_num at hs

/-- Real component VEV, unchanged d and y, only a common mass-action factor.
These precisely stated conversions do not reconcile the two matrices. -/
theorem no_common_factor (d y v k : ℂ) (hd : d ≠ 0) (hy : y ≠ 0) (hv : v ≠ 0) :
    k • NeutralMass.mass d (y*v) 0 ≠
      NeutralMass.mass d ((Real.sqrt 2 : ℂ)*(y*v)) 0 := by
  intro h
  have hr := ((common_factor_iff d (y*v) (Real.sqrt 2) k hd
    (mul_ne_zero hy hv)).mp h).2
  exact sqrt_two_ne_one hr

theorem no_common_factor_real_vev (p : Input) (k : ℂ)
    (hd : dirac p ≠ 0) (hy : p.y ≠ 0) (hv : p.v ≠ 0) (hr : star p.v = p.v) :
    k • NeutralMass.mass (dirac p) (mixing p) 0 ≠
      NeutralMass.mass (dirac p) (p.y*((Real.sqrt 2 : ℂ)*p.v)) 0 := by
  have h := no_common_factor (dirac p) p.y p.v k hd hy hv
  simpa only [mixing, hr, mul_left_comm] using h

def control : Input := ⟨1,1,1,1,1,1,1,1⟩

theorem control_nonzero : lightCoefficient control ≠ 0 := by
  rw [light_nonzero_iff]
  all_goals norm_num [control]

theorem zero_uv (p : Input) (hL : p.CL = 0) (hR : p.CR = 0) :
    lightCoefficient p = 0 :=
  NormalizedLight.zero_uv (parameters p) hL hR

end
end GUT.PatiSalam.SourceConnection
