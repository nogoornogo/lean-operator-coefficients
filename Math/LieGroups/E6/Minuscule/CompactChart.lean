import Math.LieGroups.E6.Minuscule.CompactLocalLog
import Math.Topology.LocalInverseChart
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Local exponential coordinates on the connected compact candidate

The chart is constructed from the actual real form and matrix exponential.
A linear retraction only totalizes the inverse outside its valid neighborhood.
No compact E6 global identification or manifold tangent comparison is assumed.
-/

set_option autoImplicit false

namespace Math.E6.Minuscule

noncomputable section

open NormedSpace Filter
open scoped Matrix Matrix.Norms.L2Operator Topology

def compactExp (X : compactMatrixLieAlgebra) : compactIdentityComponent :=
  ⟨MatrixLieGroupNormalizer.exponentialLine compactMatrixLieAlgebra X
      ((mem_compactMatrix_iff_exp_mem_normalizer X).mp X.property) 1,
    MatrixLieGroupNormalizer.exponentialLine_mem_identityComponent _ _ _ 1⟩

@[simp] theorem compactExp_coe (X : compactMatrixLieAlgebra) :
    ((compactExp X).val.val : Matrix27) = exp (X : Matrix27) := by
  simp [compactExp]

@[simp] theorem compactExp_zero : compactExp 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simp

theorem compactExp_continuous : Continuous compactExp := by
  let : NormedAlgebra ℚ Matrix27 := NormedAlgebra.restrictScalars ℚ ℂ _
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, compactExp_coe] using
    exp_continuous.comp (continuous_subtype_val : Continuous (fun X : compactMatrixLieAlgebra =>
      (X : Matrix27)))

attribute [local instance 100] LieRing.ofAssociativeRing

private def realFormProjection : Matrix27 →L[ℝ] compactMatrixLieAlgebra :=
  let K := compactMatrixLieAlgebra.toSubmodule
  (K.projectionOnto (Classical.choose (exists_isCompl K))
    (Classical.choose_spec (exists_isCompl K))).toContinuousLinearMap

private theorem realFormProjection_apply (X : compactMatrixLieAlgebra) :
    realFormProjection (X : Matrix27) = X :=
  Submodule.projectionOnto_apply_left _ X

/-- Total extension of the local logarithm; it agrees with the ambient logarithm near one. -/
def compactChartLog (g : compactIdentityComponent) : compactMatrixLieAlgebra :=
  realFormProjection (compactLocalLog g.val)

/-- Ambient extension used only to compute coordinate changes. -/
def compactLogExtension (A : Matrix27) : compactMatrixLieAlgebra :=
  realFormProjection (logOneAdd ℝ Matrix27 (A - 1))

theorem compactChartLog_eq_extension (g : compactIdentityComponent) :
    compactChartLog g = compactLogExtension (g.val.val : Matrix27) := rfl

theorem analyticAt_compactLogExtension (A : Matrix27)
    (hA : AnalyticAt ℝ (logOneAdd ℝ Matrix27) (A - 1)) :
    AnalyticAt ℝ compactLogExtension A := by
  have hs : AnalyticAt ℝ (fun B : Matrix27 => B - 1) A :=
    analyticAt_id.sub analyticAt_const
  exact (realFormProjection.analyticAt _).comp (hA.comp (f := fun B => B - 1) hs)

@[simp] theorem compactChartLog_one : compactChartLog 1 = 0 := by
  simp [compactChartLog, compactLocalLog]

theorem eventually_compactChartLog_coe :
    ∀ᶠ g : compactIdentityComponent in 𝓝 1,
      (compactChartLog g : Matrix27) = compactLocalLog g.val := by
  filter_upwards [(continuous_subtype_val.tendsto (1 : compactIdentityComponent)).eventually
    eventually_compactLocalLog_mem] with g hg
  exact congrArg Subtype.val (realFormProjection_apply ⟨compactLocalLog g.val, hg⟩)

theorem eventually_compactChartLog_continuousAt :
    ∀ᶠ g : compactIdentityComponent in 𝓝 1, ContinuousAt compactChartLog g := by
  have hc : Continuous (fun g : compactIdentityComponent => (g.val.val : Matrix27) - 1) :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have ht : Tendsto (fun g : compactIdentityComponent => (g.val.val : Matrix27) - 1)
      (𝓝 1) (𝓝 0) := by simpa using hc.tendsto 1
  filter_upwards [ht.eventually (analyticAt_logOneAdd ℝ Matrix27).eventually_continuousAt]
    with g hg
  have hlog : ContinuousAt (fun z : compactIdentityComponent =>
      logOneAdd ℝ Matrix27 ((z.val.val : Matrix27) - 1)) g :=
    ContinuousAt.comp (f := fun z : compactIdentityComponent => (z.val.val : Matrix27) - 1)
      hg hc.continuousAt
  exact realFormProjection.continuous.continuousAt.comp hlog

theorem eventually_compactChartLog_compactExp :
    ∀ᶠ X : compactMatrixLieAlgebra in 𝓝 0, compactChartLog (compactExp X) = X := by
  have ht : Tendsto (fun X : compactMatrixLieAlgebra => (X : Matrix27)) (𝓝 0) (𝓝 0) :=
    continuous_subtype_val.tendsto 0
  filter_upwards [ht.eventually (eventually_logOneAdd_exp_sub_one ℝ Matrix27)] with X hX
  change realFormProjection (logOneAdd ℝ Matrix27
    (((compactExp X).val.val : Matrix27) - 1)) = X
  rw [compactExp_coe, hX, realFormProjection_apply]

theorem eventually_compactExp_compactChartLog :
    ∀ᶠ g : compactIdentityComponent in 𝓝 1, compactExp (compactChartLog g) = g := by
  filter_upwards [eventually_compactChartLog_coe,
    (continuous_subtype_val.tendsto (1 : compactIdentityComponent)).eventually
      eventually_exp_compactLocalLog] with g hg he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simpa only [compactExp_coe, hg] using he

theorem eventually_analyticAt_compactMatrixLog :
    ∀ᶠ g : compactIdentityComponent in 𝓝 1,
      AnalyticAt ℝ (logOneAdd ℝ Matrix27) ((g.val.val : Matrix27) - 1) := by
  have hc : Continuous (fun g : compactIdentityComponent => (g.val.val : Matrix27) - 1) :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have ht : Tendsto (fun g : compactIdentityComponent => (g.val.val : Matrix27) - 1)
      (𝓝 1) (𝓝 0) := by simpa using hc.tendsto 1
  exact ht.eventually (analyticAt_logOneAdd ℝ Matrix27).eventually_analyticAt

theorem exists_compactExpChart :
    ∃ e : OpenPartialHomeomorph compactMatrixLieAlgebra compactIdentityComponent,
      (∀ X, e X = compactExp X) ∧ (∀ g, e.symm g = compactChartLog g) ∧
        0 ∈ e.source ∧ 1 ∈ e.target ∧
        ∀ g ∈ e.target, (compactChartLog g : Matrix27) = compactLocalLog g.val ∧
          AnalyticAt ℝ (logOneAdd ℝ Matrix27) ((g.val.val : Matrix27) - 1) := by
  obtain ⟨e, he, hi, hs, ht, _, hb⟩ :=
    LocalInverseChart.exists_chart_within compactExp compactChartLog 0 1 Set.univ
    {g | (compactChartLog g : Matrix27) = compactLocalLog g.val ∧
      AnalyticAt ℝ (logOneAdd ℝ Matrix27) ((g.val.val : Matrix27) - 1)}
    Filter.univ_mem (eventually_compactChartLog_coe.and eventually_analyticAt_compactMatrixLog)
    compactExp_zero
    (Eventually.of_forall fun _ => compactExp_continuous.continuousAt)
    eventually_compactChartLog_continuousAt eventually_compactChartLog_compactExp
    eventually_compactExp_compactChartLog
  exact ⟨e, he, hi, hs, ht, hb⟩

def compactExpChart : OpenPartialHomeomorph compactMatrixLieAlgebra compactIdentityComponent :=
  Classical.choose exists_compactExpChart

@[simp] theorem compactExpChart_apply (X : compactMatrixLieAlgebra) :
    compactExpChart X = compactExp X := (Classical.choose_spec exists_compactExpChart).1 X

@[simp] theorem compactExpChart_symm_apply (g : compactIdentityComponent) :
    compactExpChart.symm g = compactChartLog g :=
  (Classical.choose_spec exists_compactExpChart).2.1 g

theorem zero_mem_compactExpChart_source : 0 ∈ compactExpChart.source :=
  (Classical.choose_spec exists_compactExpChart).2.2.1

theorem one_mem_compactExpChart_target : 1 ∈ compactExpChart.target :=
  (Classical.choose_spec exists_compactExpChart).2.2.2.1

theorem compactExpChart_symm_coe (g : compactIdentityComponent) (hg : g ∈ compactExpChart.target) :
    (compactExpChart.symm g : Matrix27) = compactLocalLog g.val := by
  rw [compactExpChart_symm_apply]
  exact ((Classical.choose_spec exists_compactExpChart).2.2.2.2 g hg).1

theorem analyticAt_logOn_compactExpChart_target (g : compactIdentityComponent)
    (hg : g ∈ compactExpChart.target) :
    AnalyticAt ℝ (logOneAdd ℝ Matrix27) ((g.val.val : Matrix27) - 1) :=
  ((Classical.choose_spec exists_compactExpChart).2.2.2.2 g hg).2

end

end Math.E6.Minuscule
