import Math.LieGroups.E6.Minuscule.CompactChart
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Translated exponential atlas on the connected compact candidate

The topology is the existing subgroup topology. Coordinate changes are
computed using ambient matrix multiplication, exponential and logarithm.
This is not a global E6 identification or a Lie-bracket comparison.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace
open scoped Matrix Matrix.Norms.L2Operator Manifold ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing

def compactChartAt (g : compactIdentityComponent) :
    OpenPartialHomeomorph compactIdentityComponent compactMatrixLieAlgebra :=
  (Homeomorph.mulLeft g⁻¹).transOpenPartialHomeomorph compactExpChart.symm

@[simp] theorem compactChartAt_apply (g h : compactIdentityComponent) :
    compactChartAt g h = compactChartLog (g⁻¹ * h) := by
  simp [compactChartAt]

@[simp] theorem compactChartAt_symm_apply (g : compactIdentityComponent)
    (X : compactMatrixLieAlgebra) : (compactChartAt g).symm X = g * compactExp X := by
  simp [compactChartAt, Homeomorph.mulLeft_symm]

theorem compactChartAt_source (g : compactIdentityComponent) :
    (compactChartAt g).source = {h | g⁻¹ * h ∈ compactExpChart.target} := rfl

theorem compactChartAt_target (g : compactIdentityComponent) :
    (compactChartAt g).target = compactExpChart.source := rfl

theorem mem_compactChartAt_source (g : compactIdentityComponent) :
    g ∈ (compactChartAt g).source := by
  simpa only [compactChartAt_source, Set.mem_ofPred_eq, inv_mul_cancel] using
    one_mem_compactExpChart_target

@[simp] theorem compactChartAt_self (g : compactIdentityComponent) : compactChartAt g g = 0 := by
  simp

instance compactChartedSpace : ChartedSpace compactMatrixLieAlgebra compactIdentityComponent where
  atlas := Set.range compactChartAt
  chartAt := compactChartAt
  mem_chart_source := mem_compactChartAt_source
  chart_mem_atlas := fun g => ⟨g, rfl⟩

theorem compact_transition (g h : compactIdentityComponent) (X : compactMatrixLieAlgebra) :
    ((compactChartAt g).symm.trans (compactChartAt h)) X =
      compactLogExtension (((h⁻¹).val.val : Matrix27) *
        ((g.val.val : Matrix27) * exp (X : Matrix27))) := by
  simp only [OpenPartialHomeomorph.trans_apply, compactChartAt_symm_apply,
    compactChartAt_apply, compactChartLog_eq_extension]
  congr 1
  simp only [Subgroup.coe_mul, Submonoid.coe_mul, compactExp_coe]

theorem analyticAt_compact_transition (g h : compactIdentityComponent)
    (X : compactMatrixLieAlgebra)
    (hX : X ∈ ((compactChartAt g).symm.trans (compactChartAt h)).source) :
    AnalyticAt ℝ ((compactChartAt g).symm.trans (compactChartAt h)) X := by
  have hm : h⁻¹ * (g * compactExp X) ∈ compactExpChart.target := by
    simpa only [compactChartAt_source, Set.mem_preimage, Set.mem_ofPred_eq,
      OpenPartialHomeomorph.symm_symm,
      compactChartAt_symm_apply] using hX.2
  have ha := analyticAt_logOn_compactExpChart_target _ hm
  have hcoe : ((h⁻¹ * (g * compactExp X)).val.val : Matrix27) =
      ((h⁻¹).val.val : Matrix27) * ((g.val.val : Matrix27) * exp (X : Matrix27)) := by
    simp only [Subgroup.coe_mul, Submonoid.coe_mul, compactExp_coe]
  rw [hcoe] at ha
  have he : AnalyticAt ℝ (fun Y : compactMatrixLieAlgebra => exp (Y : Matrix27)) X :=
    (exp_analytic (𝕂 := ℝ) _).comp (compactMatrixLieAlgebra.toSubmodule.subtypeL.analyticAt X)
  have hm : AnalyticAt ℝ (fun Y : compactMatrixLieAlgebra =>
      ((h⁻¹).val.val : Matrix27) * ((g.val.val : Matrix27) * exp (Y : Matrix27))) X :=
    analyticAt_const.mul (analyticAt_const.mul he)
  have hf := (analyticAt_compactLogExtension _ ha).comp
    (f := fun Y : compactMatrixLieAlgebra =>
      ((h⁻¹).val.val : Matrix27) * ((g.val.val : Matrix27) * exp (Y : Matrix27))) hm
  simpa only [Function.comp_def, ← compact_transition] using hf

instance compactIsManifold : IsManifold 𝓘(ℝ, compactMatrixLieAlgebra) ∞
    compactIdentityComponent := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨g, rfl⟩ ⟨h, rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id_eq, Set.range_id, Set.inter_univ]
  exact fun X hX => (analyticAt_compact_transition g h X hX).contDiffAt.contDiffWithinAt

/-- The ambient derivative of the exponential parametrization is the real-form inclusion. -/
theorem compactExp_hasStrictFDerivAt_zero :
    HasStrictFDerivAt (fun X : compactMatrixLieAlgebra =>
      ((compactExp X).val.val : Matrix27)) compactMatrixLieAlgebra.toSubmodule.subtypeL 0 := by
  convert! (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Matrix27)).comp 0
      compactMatrixLieAlgebra.toSubmodule.subtypeL.hasStrictFDerivAt using 1
  funext X
  exact compactExp_coe X

end

end Math.E6.Minuscule
