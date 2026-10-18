import Physics.StandardModel.Operators.SixQuarkConventionalBasis
import Math.RepresentationTheory.SixSlotSpeciesSum

open Math

/-! Actual exterior evaluations of the conventional operators. -/
namespace GUT.SixQuarkConventionalCoordinates
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor SixQuarkInvariant SixQuarkTwoCoordinates
open SixQuarkConventionalBasis SixQuarkSpeciesQuotient
open scoped TensorProduct
attribute [local irreducible] orderedLift
attribute [local irreducible] SixSlotAlternation.alternating SixSlotSpeciesSum.blockSum

theorem blockAlternation_eq (F : (Color × Spin) → (Color × Spin) →
    (Color × Spin) → (Color × Spin) → (Color × Spin) → (Color × Spin) → ℂ)
    (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    DeltaBTwoContractionRelations.blockAlternation F u d =
      SixSlotSpeciesSum.blockSum F u d := by
  exact DeltaBTwoContractionRelations.blockAlternation_eq F u d

theorem descend_block (f : Coefficient) (hf : IsInvariant f)
    (v : Fin 6 → Quark) :
    exteriorRestriction (descend f hf).1 v =
      SixSlotSpeciesSum.blockSum
        (fun a b c d e x => f ![a,b,c,d,e,x])
        ![v 0, v 2] ![v 1, v 3, v 4, v 5] := by
  rw [exteriorRestriction_apply]
  change SixSlotAlternation.coefficient _ _ _ _ = _
  rw [SixSlotAlternation.coefficient_apply_ιMulti]
  rw [orderedIntertwiner_toLinearMap]
  have he := SixSlotSpeciesSum.alternating_slots_block (orderedLift f)
      ![v 0,v 2] ![v 1,v 3,v 4,v 5]
  simp only [orderedLift_apply] at he
  exact he

private theorem pure_vector (a : Fin 6 → Color) (s : Fin 6 → Spin) :
    ![a 0 ⊗ₜ[ℂ] s 0, a 1 ⊗ₜ[ℂ] s 1, a 2 ⊗ₜ[ℂ] s 2,
      a 3 ⊗ₜ[ℂ] s 3, a 4 ⊗ₜ[ℂ] s 4, a 5 ⊗ₜ[ℂ] s 5] =
      (fun i => a i ⊗ₜ[ℂ] s i) := by
  ext i; fin_cases i <;> rfl

private theorem O1_pure (a b c d e x : Color) (s t u v w y : Spin) :
    orderedO1 ![a ⊗ₜ[ℂ] s,b ⊗ₜ[ℂ] t,c ⊗ₜ[ℂ] u,d ⊗ₜ[ℂ] v,
      e ⊗ₜ[ℂ] w,x ⊗ₜ[ℂ] y] =
    DeltaBTwoContractionRelations.orderedO1Value a b c d e x s t u v w y := by
  have he := pure_vector ![a,b,c,d,e,x] ![s,t,u,v,w,y]
  change ![a ⊗ₜ[ℂ] s,b ⊗ₜ[ℂ] t,c ⊗ₜ[ℂ] u,d ⊗ₜ[ℂ] v,
    e ⊗ₜ[ℂ] w,x ⊗ₜ[ℂ] y] = _ at he
  rw [he]
  exact orderedO1_apply _ _

private theorem O2_pure (a b c d e x : Color) (s t u v w y : Spin) :
    orderedO2 ![a ⊗ₜ[ℂ] s,b ⊗ₜ[ℂ] t,c ⊗ₜ[ℂ] u,d ⊗ₜ[ℂ] v,
      e ⊗ₜ[ℂ] w,x ⊗ₜ[ℂ] y] =
    DeltaBTwoContractionRelations.orderedO2Value a b c d e x s t u v w y := by
  have he := pure_vector ![a,b,c,d,e,x] ![s,t,u,v,w,y]
  change ![a ⊗ₜ[ℂ] s,b ⊗ₜ[ℂ] t,c ⊗ₜ[ℂ] u,d ⊗ₜ[ℂ] v,
    e ⊗ₜ[ℂ] w,x ⊗ₜ[ℂ] y] = _ at he
  rw [he]
  exact orderedO2_apply _ _

private theorem O3_pure (a b c d e x : Color) (s t u v w y : Spin) :
    orderedO3 ![a ⊗ₜ[ℂ] s,b ⊗ₜ[ℂ] t,c ⊗ₜ[ℂ] u,d ⊗ₜ[ℂ] v,
      e ⊗ₜ[ℂ] w,x ⊗ₜ[ℂ] y] =
    DeltaBTwoContractionRelations.orderedO3Value a b c d e x s t u v w y := by
  have he := pure_vector ![a,b,c,d,e,x] ![s,t,u,v,w,y]
  change ![a ⊗ₜ[ℂ] s,b ⊗ₜ[ℂ] t,c ⊗ₜ[ℂ] u,d ⊗ₜ[ℂ] v,
    e ⊗ₜ[ℂ] w,x ⊗ₜ[ℂ] y] = _ at he
  rw [he]
  exact orderedO3_apply _ _

private theorem descend_pure_block (f : Coefficient) (hf : IsInvariant f)
    (F : (Color × Spin) → (Color × Spin) → (Color × Spin) →
      (Color × Spin) → (Color × Spin) → (Color × Spin) → ℂ)
    (he : ∀ a b c d e x : Color × Spin,
      f ![a.1 ⊗ₜ[ℂ] a.2,b.1 ⊗ₜ[ℂ] b.2,c.1 ⊗ₜ[ℂ] c.2,
        d.1 ⊗ₜ[ℂ] d.2,e.1 ⊗ₜ[ℂ] e.2,x.1 ⊗ₜ[ℂ] x.2] = F a b c d e x)
    (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    exteriorRestriction (descend f hf).1
      ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (d 0).1 ⊗ₜ[ℂ] (d 0).2,
        (u 1).1 ⊗ₜ[ℂ] (u 1).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,
        (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2] =
      DeltaBTwoContractionRelations.blockAlternation F u d := by
  rw [descend_block, blockAlternation_eq]
  change SixSlotSpeciesSum.blockSum _
    ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (u 1).1 ⊗ₜ[ℂ] (u 1).2]
    ![(d 0).1 ⊗ₜ[ℂ] (d 0).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,
      (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2] = _
  have hu : ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (u 1).1 ⊗ₜ[ℂ] (u 1).2] =
      (fun i => (u i).1 ⊗ₜ[ℂ] (u i).2) := by ext i; fin_cases i <;> rfl
  have hd : ![(d 0).1 ⊗ₜ[ℂ] (d 0).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,
      (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2] =
      (fun i => (d i).1 ⊗ₜ[ℂ] (d i).2) := by ext i; fin_cases i <;> rfl
  rw [hu, hd]
  simp only [SixSlotSpeciesSum.blockSum, he]

theorem O1_block (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    exteriorRestriction O1.1
      ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (d 0).1 ⊗ₜ[ℂ] (d 0).2,
        (u 1).1 ⊗ₜ[ℂ] (u 1).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,
        (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2] =
      DeltaBTwoContractionRelations.blockAlternation
        DeltaBTwoContractionRelations.valueO1 u d :=
  descend_pure_block _ _ _ (fun _ _ _ _ _ _ => O1_pure _ _ _ _ _ _ _ _ _ _ _ _) u d

theorem O2_block (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    exteriorRestriction O2.1
      ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (d 0).1 ⊗ₜ[ℂ] (d 0).2,
        (u 1).1 ⊗ₜ[ℂ] (u 1).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,
        (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2] =
      DeltaBTwoContractionRelations.blockAlternation
        DeltaBTwoContractionRelations.valueO2 u d :=
  descend_pure_block _ _ _ (fun _ _ _ _ _ _ => O2_pure _ _ _ _ _ _ _ _ _ _ _ _) u d

theorem O3_block (u : Fin 2 → Color × Spin) (d : Fin 4 → Color × Spin) :
    exteriorRestriction O3.1
      ![(u 0).1 ⊗ₜ[ℂ] (u 0).2, (d 0).1 ⊗ₜ[ℂ] (d 0).2,
        (u 1).1 ⊗ₜ[ℂ] (u 1).2, (d 1).1 ⊗ₜ[ℂ] (d 1).2,
        (d 2).1 ⊗ₜ[ℂ] (d 2).2, (d 3).1 ⊗ₜ[ℂ] (d 3).2] =
      DeltaBTwoContractionRelations.blockAlternation
        DeltaBTwoContractionRelations.valueO3 u d :=
  descend_pure_block _ _ _ (fun _ _ _ _ _ _ => O3_pure _ _ _ _ _ _ _ _ _ _ _ _) u d

theorem probes_O1 : twoCoordinateEquiv O1 = ![0,48] := by
  rw [twoCoordinateEquiv_apply]
  ext i; fin_cases i <;>
    simp only [twoProbes, Matrix.cons_val_zero, Matrix.cons_val_one, O1,
      descend_block]
  all_goals
    simp [SixSlotSpeciesSum.blockSum, Fin.sum_univ_succ,
      SixSlotSpeciesSum.downIndex, SixSlotSpeciesSum.downParity,
      O1_pure, DeltaBTwoContractionRelations.orderedO1Value,
      DeltaBTwoContractionRelations.colorSSS, eps3, eps2, colorBasis,
      weakBasis, Fin.ext_iff]
  all_goals norm_num

theorem probes_O2 : twoCoordinateEquiv O2 = ![48,-12] := by
  rw [twoCoordinateEquiv_apply]
  ext i; fin_cases i <;>
    simp only [twoProbes, Matrix.cons_val_zero, Matrix.cons_val_one, O2,
      descend_block]
  all_goals
    simp [SixSlotSpeciesSum.blockSum, Fin.sum_univ_succ,
      SixSlotSpeciesSum.downIndex, SixSlotSpeciesSum.downParity,
      O2_pure, DeltaBTwoContractionRelations.orderedO2Value,
      DeltaBTwoContractionRelations.colorSSS, eps3, eps2, colorBasis,
      weakBasis, Fin.ext_iff]
    norm_num

theorem probes_O3 : twoCoordinateEquiv O3 = ![16,-20] := by
  rw [twoCoordinateEquiv_apply]
  ext i; fin_cases i <;>
    simp only [twoProbes, Matrix.cons_val_zero, Matrix.cons_val_one, O3,
      descend_block]
  all_goals
    simp [SixSlotSpeciesSum.blockSum, Fin.sum_univ_succ,
      SixSlotSpeciesSum.downIndex, SixSlotSpeciesSum.downParity,
      O3_pure, DeltaBTwoContractionRelations.orderedO3Value,
      DeltaBTwoContractionRelations.colorAAS,
      eps3, eps2, colorBasis, weakBasis, Fin.ext_iff]
    norm_num

theorem conventional_determinant :
    (16 : ℂ) * (-12) - 48 * (-20) = 768 := by norm_num

/-- The Fierz relation holds on the intrinsic physical degree sector. -/
theorem fierz : O2 - O1 = (3 : ℂ) • O3 := by
  apply twoCoordinateEquiv.injective
  simp only [map_sub, map_smul, probes_O1, probes_O2, probes_O3]
  ext i; fin_cases i <;> norm_num

/-- Coordinates ordered as AAS (O3), then SSS (O2). -/
def conventionalEquiv : Sector ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := ![-twoCoordinateEquiv f 0 / 64 - twoCoordinateEquiv f 1 / 16,
    5 * twoCoordinateEquiv f 0 / 192 + twoCoordinateEquiv f 1 / 48]
  invFun z := z 0 • O3 + z 1 • O2
  left_inv f := by
    apply twoCoordinateEquiv.injective
    simp only [map_add, map_smul, probes_O3, probes_O2]
    ext i; fin_cases i <;> simp [smul_eq_mul]
    all_goals ring
  right_inv z := by
    simp only [map_add, map_smul, probes_O3, probes_O2]
    ext i; fin_cases i <;> simp [smul_eq_mul]
    all_goals ring
  map_add' f g := by
    simp only [map_add]
    ext i; fin_cases i <;> simp <;> ring
  map_smul' z f := by
    simp only [map_smul]
    ext i; fin_cases i <;> simp [smul_eq_mul]
    all_goals ring

theorem reconstruct (f : Sector) :
    f = (conventionalEquiv f 0) • O3 + (conventionalEquiv f 1) • O2 :=
  (conventionalEquiv.symm_apply_apply f).symm

def Q1 : Sector := (-4 : ℂ) • O3
def Q4 : Sector := (-4 / 5 : ℂ) • O1 + (-16 / 5 : ℂ) • O2

theorem probes_Q1 : twoCoordinateEquiv Q1 = ![-64,80] := by
  simp only [Q1, map_smul, probes_O3]
  ext i; fin_cases i <;> norm_num

theorem probes_Q4 : twoCoordinateEquiv Q4 = ![-768/5,0] := by
  simp only [Q4, map_add, map_smul, probes_O1, probes_O2]
  ext i; fin_cases i <;> norm_num

/-- The conventional chiral Q1/Q4 normalization, with explicit probe inverse. -/
def chiralEquiv : Sector ≃ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := ![twoCoordinateEquiv f 1 / 80,
    -(5 * twoCoordinateEquiv f 0 + 4 * twoCoordinateEquiv f 1) / 768]
  invFun z := z 0 • Q1 + z 1 • Q4
  left_inv f := by
    apply twoCoordinateEquiv.injective
    simp only [map_add, map_smul, probes_Q1, probes_Q4]
    ext i; fin_cases i <;> simp [smul_eq_mul]
    all_goals ring
  right_inv z := by
    simp only [map_add, map_smul, probes_Q1, probes_Q4]
    ext i; fin_cases i <;> simp [smul_eq_mul]
    all_goals ring
  map_add' f g := by
    simp only [map_add]
    ext i; fin_cases i <;> simp <;> ring
  map_smul' z f := by
    simp only [map_smul]
    ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

theorem reconstruct_chiral (f : Sector) :
    f = (chiralEquiv f 0) • Q1 + (chiralEquiv f 1) • Q4 :=
  (chiralEquiv.symm_apply_apply f).symm

end
end GUT.SixQuarkConventionalCoordinates
