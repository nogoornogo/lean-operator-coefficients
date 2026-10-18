import Math.RepresentationTheory.Unitary.ContinuousAction
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-! # Haar-averaged invariant Hermitian forms -/

namespace Math.CompactRepresentationUnitarization
open ContinuousRepresentationScope MeasureTheory TopologicalSpace
open scoped ComplexConjugate
noncomputable section

section CompactGroup

variable {G E : Type*}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [CompactSpace G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- Haar measure normalized on the whole compact group. -/
def normalizedHaar : Measure G :=
  Measure.haarMeasure (⊤ : PositiveCompacts G)

instance normalizedHaar_isHaarMeasure :
    Measure.IsHaarMeasure (normalizedHaar (G := G)) := by
  unfold normalizedHaar
  infer_instance

instance normalizedHaar_isProbabilityMeasure :
    IsProbabilityMeasure (normalizedHaar (G := G)) where
  measure_univ := by
    change Measure.haarMeasure (⊤ : PositiveCompacts G) Set.univ = 1
    rw [← PositiveCompacts.coe_top]
    exact Measure.haarMeasure_self

variable (rho : Representation ℂ G E)
/-- The orbit inner-product integrand.  The inverse is what lets left Haar
invariance prove invariance under the original representation. -/
def orbitInner (v w : E) (g : G) : ℂ :=
  inner ℂ (rho g⁻¹ v) (rho g⁻¹ w)

omit [MeasurableSpace G] [BorelSpace G] [CompactSpace G] [FiniteDimensional ℂ E] in
theorem orbitInner_continuous
    (hContinuous : IsJointlyContinuous rho) (v w : E) :
    Continuous (orbitInner rho v w) := by
  exact
    ((hContinuous.orbit v).comp continuous_inv).inner
      ((hContinuous.orbit w).comp continuous_inv)

omit [FiniteDimensional ℂ E] in
theorem orbitInner_integrable
    (hContinuous : IsJointlyContinuous rho) (v w : E) :
    Integrable (orbitInner rho v w) (normalizedHaar (G := G)) :=
  (orbitInner_continuous rho hContinuous v w).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The Haar-averaged Hermitian form. -/
def averagedInner (v w : E) : ℂ :=
  ∫ g, orbitInner rho v w g ∂(normalizedHaar (G := G))

omit [FiniteDimensional ℂ E] in
theorem averagedInner_conj_symm (v w : E) :
    conj (averagedInner rho v w) = averagedInner rho w v := by
  unfold averagedInner
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with g
  exact inner_conj_symm _ _

omit [FiniteDimensional ℂ E] in
theorem averagedInner_add_left
    (hContinuous : IsJointlyContinuous rho) (u v w : E) :
    averagedInner rho (u + v) w =
      averagedInner rho u w + averagedInner rho v w := by
  simp only [averagedInner, orbitInner, map_add, inner_add_left]
  exact integral_add
    (orbitInner_integrable rho hContinuous u w)
    (orbitInner_integrable rho hContinuous v w)

omit [FiniteDimensional ℂ E] in
theorem averagedInner_smul_left (u v : E) (c : ℂ) :
    averagedInner rho (c • u) v = conj c * averagedInner rho u v := by
  simp only [averagedInner, orbitInner, map_smul, inner_smul_left]
  exact integral_const_mul (conj c)
    (fun g => inner ℂ (rho g⁻¹ u) (rho g⁻¹ v))

omit [FiniteDimensional ℂ E] in
theorem averagedInner_re_self
    (hContinuous : IsJointlyContinuous rho) (v : E) :
    (averagedInner rho v v).re =
      ∫ g, ‖rho g⁻¹ v‖ ^ 2 ∂(normalizedHaar (G := G)) := by
  unfold averagedInner
  calc
    (∫ g, orbitInner rho v v g ∂(normalizedHaar (G := G))).re =
        ∫ g, (orbitInner rho v v g).re
          ∂(normalizedHaar (G := G)) :=
      (integral_re (orbitInner_integrable rho hContinuous v v)).symm
    _ = ∫ g, ‖rho g⁻¹ v‖ ^ 2 ∂(normalizedHaar (G := G)) := by
      apply integral_congr_ae
      filter_upwards [] with g
      simpa only [orbitInner, RCLike.re_to_complex] using
        (inner_self_eq_norm_sq (𝕜 := ℂ) (rho g⁻¹ v))

omit [FiniteDimensional ℂ E] in
theorem averagedInner_re_nonneg
    (hContinuous : IsJointlyContinuous rho) (v : E) :
    0 ≤ (averagedInner rho v v).re := by
  rw [averagedInner_re_self rho hContinuous v]
  exact integral_nonneg fun _ => sq_nonneg _

omit [FiniteDimensional ℂ E] in
theorem averagedInner_re_pos
    (hContinuous : IsJointlyContinuous rho) {v : E} (hv : v ≠ 0) :
    0 < (averagedInner rho v v).re := by
  rw [averagedInner_re_self rho hContinuous v]
  let f : G → ℝ := fun g => ‖rho g⁻¹ v‖ ^ 2
  have hfContinuous : Continuous f := by
    exact (((hContinuous.orbit v).comp continuous_inv).norm).pow 2
  have hfIntegrable : Integrable f (normalizedHaar (G := G)) :=
    hfContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfNonneg : 0 ≤ f := fun _ => sq_nonneg _
  have hfOne : f (1 : G) ≠ 0 := by
    simp only [f, inv_one, map_one, Module.End.one_apply, ne_eq, sq_eq_zero_iff,
      norm_eq_zero]
    exact hv
  exact integral_pos_of_integrable_nonneg_nonzero
    hfContinuous hfIntegrable hfNonneg hfOne

omit [FiniteDimensional ℂ E] in
theorem averagedInner_definite
    (hContinuous : IsJointlyContinuous rho) (v : E)
    (hv : averagedInner rho v v = 0) : v = 0 := by
  by_contra hv0
  have hpos := averagedInner_re_pos rho hContinuous hv0
  rw [hv] at hpos
  simp at hpos

/-- The positive-definite Hermitian core obtained by compact averaging. -/
@[instance_reducible]
def averagedInnerCore
    (hContinuous : IsJointlyContinuous rho) : InnerProductSpace.Core ℂ E where
  inner := averagedInner rho
  conj_inner_symm := fun x y => averagedInner_conj_symm rho y x
  re_inner_nonneg := averagedInner_re_nonneg rho hContinuous
  add_left := averagedInner_add_left rho hContinuous
  smul_left := averagedInner_smul_left rho
  definite := averagedInner_definite rho hContinuous

omit [FiniteDimensional ℂ E] in
theorem averagedInner_invariant
    (k : G) (v w : E) :
    averagedInner rho (rho k v) (rho k w) = averagedInner rho v w := by
  let f : G → ℂ := orbitInner rho v w
  calc
    averagedInner rho (rho k v) (rho k w) =
        ∫ g, f (k⁻¹ * g) ∂(normalizedHaar (G := G)) := by
      apply integral_congr_ae
      filter_upwards [] with g
      simp only [f, orbitInner, mul_inv_rev, inv_inv]
      have hv : rho g⁻¹ (rho k v) = rho (g⁻¹ * k) v := by
        rw [← Module.End.mul_apply, ← map_mul]
      have hw : rho g⁻¹ (rho k w) = rho (g⁻¹ * k) w := by
        rw [← Module.End.mul_apply, ← map_mul]
      rw [hv, hw]
    _ = ∫ g, f g ∂(normalizedHaar (G := G)) :=
      integral_mul_left_eq_self f k⁻¹
    _ = averagedInner rho v w := rfl

end CompactGroup

end
end Math.CompactRepresentationUnitarization
