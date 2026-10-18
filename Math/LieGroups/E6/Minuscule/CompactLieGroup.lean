import Math.LieGroups.E6.Minuscule.CompactAtlas
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth group operations on the connected compact candidate

Smoothness is proved by the actual matrix inclusion and local logarithm.
The global E6 form and tangent Lie-bracket identification remain separate.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing

def compactMatrix (g : compactIdentityComponent) : Matrix27 := g.val.val

@[simp] theorem compactMatrix_one : compactMatrix 1 = 1 := rfl

@[simp] theorem compactMatrix_mul (g h : compactIdentityComponent) :
    compactMatrix (g * h) = compactMatrix g * compactMatrix h := rfl

@[simp] theorem compactMatrix_inv (g : compactIdentityComponent) :
    compactMatrix g⁻¹ = star (compactMatrix g) := rfl

theorem compactMatrix_continuous : Continuous compactMatrix :=
  continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem compactMatrix_injective : Function.Injective compactMatrix :=
  fun _ _ h => Subtype.ext (Subtype.ext (Subtype.ext h))

theorem compact_extChartAt_apply (g h : compactIdentityComponent) :
    extChartAt 𝓘(ℝ, compactMatrixLieAlgebra) g h = compactChartLog (g⁻¹ * h) :=
  compactChartAt_apply g h

theorem compact_extChartAt_symm_apply (g : compactIdentityComponent) (X : compactMatrixLieAlgebra) :
    (extChartAt 𝓘(ℝ, compactMatrixLieAlgebra) g).symm X = g * compactExp X :=
  compactChartAt_symm_apply g X

theorem contMDiff_compactMatrix :
    ContMDiff 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, Matrix27) ∞ compactMatrix := by
  intro g
  rw [contMDiffAt_iff_source]
  have he : AnalyticAt ℝ (fun X : compactMatrixLieAlgebra => exp (X : Matrix27)) 0 :=
    (exp_analytic (𝕂 := ℝ) _).comp (compactMatrixLieAlgebra.toSubmodule.subtypeL.analyticAt 0)
  have hm : AnalyticAt ℝ (fun X : compactMatrixLieAlgebra =>
      compactMatrix g * exp (X : Matrix27)) 0 := analyticAt_const.mul he
  simpa only [modelWithCornersSelf_coe, Set.range_id, contMDiffWithinAt_univ,
    Function.comp_def, compact_extChartAt_symm_apply, compact_extChartAt_apply,
    inv_mul_cancel, compactChartLog_one, compactMatrix_mul, compactMatrix, compactExp_coe,
    Subgroup.coe_mul, Submonoid.coe_mul] using
    hm.contDiffAt.contMDiffAt (n := ∞)

section FromMatrices

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} {f : M → compactIdentityComponent} {x : M}

theorem contMDiffAt_of_compactMatrix (hc : ContinuousAt f x)
    (hf : ContMDiffAt I 𝓘(ℝ, Matrix27) ∞ (compactMatrix ∘ f) x) :
    ContMDiffAt I 𝓘(ℝ, compactMatrixLieAlgebra) ∞ f x := by
  rw [contMDiffAt_iff_target]
  refine ⟨hc, ?_⟩
  let g := f x
  have hi : compactMatrix g⁻¹ * compactMatrix g = 1 := by
    rw [← compactMatrix_mul, inv_mul_cancel, compactMatrix_one]
  have hl : AnalyticAt ℝ compactLogExtension (compactMatrix g⁻¹ * compactMatrix g) := by
    apply analyticAt_compactLogExtension
    simpa only [hi, sub_self] using analyticAt_logOneAdd ℝ Matrix27
  have hm : AnalyticAt ℝ (fun A : Matrix27 => compactMatrix g⁻¹ * A) (compactMatrix g) :=
    analyticAt_const.mul analyticAt_id
  have ha := hl.comp (f := fun A : Matrix27 => compactMatrix g⁻¹ * A) hm
  have hh := ha.contDiffAt.contMDiffAt.comp x hf
  simpa only [Function.comp_def, compact_extChartAt_apply, compactChartLog_eq_extension,
    compactMatrix, Subgroup.coe_mul, Submonoid.coe_mul] using hh

end FromMatrices

theorem contMDiff_compact_mul :
    ContMDiff (𝓘(ℝ, compactMatrixLieAlgebra).prod 𝓘(ℝ, compactMatrixLieAlgebra))
      𝓘(ℝ, compactMatrixLieAlgebra) ∞ (fun p : compactIdentityComponent × compactIdentityComponent =>
        p.1 * p.2) := by
  intro p
  apply contMDiffAt_of_compactMatrix (continuous_mul.continuousAt)
  have h1 : ContMDiff (𝓘(ℝ, compactMatrixLieAlgebra).prod 𝓘(ℝ, compactMatrixLieAlgebra))
      𝓘(ℝ, Matrix27) ∞ (fun q : compactIdentityComponent × compactIdentityComponent =>
        compactMatrix q.1) := contMDiff_compactMatrix.comp contMDiff_fst
  have h2 : ContMDiff (𝓘(ℝ, compactMatrixLieAlgebra).prod 𝓘(ℝ, compactMatrixLieAlgebra))
      𝓘(ℝ, Matrix27) ∞ (fun q : compactIdentityComponent × compactIdentityComponent =>
        compactMatrix q.2) := contMDiff_compactMatrix.comp contMDiff_snd
  have hm : ContDiff ℝ ∞ (fun q : Matrix27 × Matrix27 => q.1 * q.2) :=
    contDiff_fst.mul contDiff_snd
  have hp : ContMDiff (𝓘(ℝ, compactMatrixLieAlgebra).prod 𝓘(ℝ, compactMatrixLieAlgebra))
      𝓘(ℝ, Matrix27 × Matrix27) ∞ (fun q : compactIdentityComponent × compactIdentityComponent =>
        (compactMatrix q.1, compactMatrix q.2)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h1.prodMk h2
  simpa only [Function.comp_def, compactMatrix_mul] using
    (hm.contMDiff.comp hp).contMDiffAt (x := p)

theorem contMDiff_compact_inv :
    ContMDiff 𝓘(ℝ, compactMatrixLieAlgebra) 𝓘(ℝ, compactMatrixLieAlgebra) ∞
      (fun g : compactIdentityComponent => g⁻¹) := by
  intro g
  apply contMDiffAt_of_compactMatrix continuous_inv.continuousAt
  have hs : ContDiff ℝ ∞ (star : Matrix27 → Matrix27) :=
    (starL ℝ : Matrix27 ≃L[ℝ] Matrix27).contDiff
  simpa only [Function.comp_def, compactMatrix_inv] using
    (hs.contMDiff.comp contMDiff_compactMatrix).contMDiffAt (x := g)

instance compactLieGroup : LieGroup 𝓘(ℝ, compactMatrixLieAlgebra) ∞ compactIdentityComponent where
  contMDiff_mul := contMDiff_compact_mul
  contMDiff_inv := contMDiff_compact_inv

end

end Math.E6.Minuscule
