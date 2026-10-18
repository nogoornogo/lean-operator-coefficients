import GUT.PatiSalam.Matching.ModelApplication
import GUT.PatiSalam.Matching.NeutralMass
import Math.LinearAlgebra.LightLineNormalization

/-! Normalization in the supplied canonical Euclidean kinetic form.
The underlying holomorphic mass convention is still an explicit component input. -/
namespace GUT.PatiSalam.NormalizedLight
noncomputable section
open Math
abbrev Neutral := EuclideanSpace ℂ (Fin 3)

def chart (d M : ℂ) : Neutral := WithLp.toLp 2 (NeutralMass.mode d M)

def massMap (d M : ℂ) : Neutral →ₗ[ℂ] (Fin 3 → ℂ) :=
  (Matrix.mulVecLin (NeutralMass.mass d M 0)).comp
    (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin 3)).toLinearMap

theorem chart_nonzero (d M : ℂ) : chart d M ≠ 0 := by
  intro hz
  apply NeutralMass.mode_nonzero d M
  have h := congrArg (fun z : Neutral => z.ofLp) hz
  simpa [chart] using h

def scale (d M : ℂ) := LightLineNormalization.scale (chart d M)
def unitMode (d M : ℂ) := LightLineNormalization.unit (chart d M)

theorem scale_nonzero (d M : ℂ) : scale d M ≠ 0 :=
  LightLineNormalization.scale_ne_zero _ (chart_nonzero d M)

theorem unit_norm (d M : ℂ) : ‖unitMode d M‖ = 1 :=
  LightLineNormalization.unit_norm _ (chart_nonzero d M)

theorem unit_kernel (d M : ℂ) (hM : M ≠ 0) : massMap d M (unitMode d M) = 0 := by
  apply LightLineNormalization.unit_mem_kernel
  exact NeutralMass.exact_zero_mode d M hM

theorem unit_coordinate (d M : ℂ) (i : Fin 3) :
    unitMode d M i = scale d M * NeutralMass.mode d M i := by rfl

def barredProjection (d M : ℂ) := star (unitMode d M 2)

theorem barred_projection (d M : ℂ) :
    barredProjection d M = star (scale d M) * star (-d/M) := by
  rw [barredProjection, unit_coordinate, star_mul]
  simp only [NeutralMass.mode, Matrix.cons_val_two]
  exact mul_comm _ _

theorem barred_nonzero_iff (d M : ℂ) (hM : M ≠ 0) :
    barredProjection d M ≠ 0 ↔ d ≠ 0 := by
  rw [barred_projection, mul_ne_zero_iff]
  simp [scale_nonzero, hM]

/-- Scale only the anti-neutrino coordinate; the quark coordinates are unchanged. -/
def lightChange (d M : ℂ) : LightFields.Light ≃ₗ[ℂ] LightFields.Light :=
  LinearEquiv.prodCongr (LinearEquiv.refl ℂ (Fin 4 → LightFields.Quark))
    (LinearEquiv.smulOfNeZero ℂ GUT.WeylSpinor.Space
      (star (scale d M)) (star_ne_zero.mpr (scale_nonzero d M)))

def injection (d M : ℂ) := LightFields.injection.comp (lightChange d M).toLinearMap

def coefficient (p : ModelApplication.Parameters) :=
  MixedSingleBosonEvaluation.pull (ModelApplication.smCoefficient p).toLinearMap
    (Pi.single (1 : GUT.BnvMixedInput.ScalarSpecies) (p.w • TypedVertex.neutralHiggs))
    (injection (p.Y*star p.w) p.M)

theorem coefficient_eq (p : ModelApplication.Parameters) : coefficient p =
    (ModelApplication.lightCoefficient p).compLinearMap
      (lightChange (p.Y*star p.w) p.M).toLinearMap := by
  ext v
  rfl

theorem nonzero_iff (p : ModelApplication.Parameters)
    (hL : p.Lambda ≠ 0) (hm : p.m ≠ 0) (hM : p.M ≠ 0) :
    coefficient p ≠ 0 ↔ p.w ≠ 0 ∧ p.v ≠ 0 ∧ p.y ≠ 0 ∧ p.Y ≠ 0 ∧
      (p.CL ≠ 0 ∨ p.CR ≠ 0) := by
  rw [coefficient_eq, LightLineNormalization.comp_equiv_ne_zero_iff]
  exact ModelApplication.light_nonzero_iff p hL hm hM

/-- Specialize the neutral entry to the literal component contraction.
This does not identify it with Eq.(12)'s displayed source convention. -/
theorem literal_nonzero_iff (p : ModelApplication.Parameters)
    (hL : p.Lambda ≠ 0) (hm : p.m ≠ 0) (hy : p.y ≠ 0) (hv : p.v ≠ 0) :
    coefficient {p with M := p.y*star p.v} ≠ 0 ↔
      p.w ≠ 0 ∧ p.Y ≠ 0 ∧ (p.CL ≠ 0 ∨ p.CR ≠ 0) := by
  rw [nonzero_iff {p with M := p.y*star p.v} hL hm
    (mul_ne_zero hy (star_ne_zero.mpr hv))]
  simp [hy, hv]

theorem control_nonzero : coefficient ModelApplication.control ≠ 0 := by
  rw [nonzero_iff]
  all_goals norm_num [ModelApplication.control]

theorem zero_uv (p : ModelApplication.Parameters) (hL : p.CL = 0) (hR : p.CR = 0) :
    coefficient p = 0 := by
  rw [coefficient_eq, ModelApplication.zero_uv p hL hR]
  ext v
  rfl

end
end GUT.PatiSalam.NormalizedLight
