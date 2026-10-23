import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkSpeciesQuotient

open Math

/-! Intrinsic degree `(2,4)` coefficients and their two-probe inverse. -/
namespace Physics.SixQuarkTwoCoordinates
set_option autoImplicit false
noncomputable section
open SMEpsilonTensor SixQuarkInvariant SixQuarkSpeciesQuotient
open Representation
open scoped TensorProduct

private def curried (f : Coefficient) :
    Quark →ₗ[ℂ] Quark →ₗ[ℂ] Quark →ₗ[ℂ] Quark →ₗ[ℂ] Quark →ₗ[ℂ] Quark →ₗ[ℂ] ℂ :=
  f.curryRight.curryRight.curryRight.curryRight.curryRight.curryRight Fin.elim0

private def firstPair (f : Coefficient) :
    (Quark ⊗[ℂ] Quark) →ₗ[ℂ] Quark →ₗ[ℂ] Quark →ₗ[ℂ]
      Quark →ₗ[ℂ] Quark →ₗ[ℂ] ℂ := TensorProduct.lift (curried f)

private def secondPair (f : Coefficient) :
    (Quark ⊗[ℂ] Quark) →ₗ[ℂ] (Quark ⊗[ℂ] Quark) →ₗ[ℂ]
      Quark →ₗ[ℂ] Quark →ₗ[ℂ] ℂ where
  toFun p := TensorProduct.lift (firstPair f p)
  map_add' p q := by ext x y z w; simp [firstPair]
  map_smul' z p := by ext x y v w; simp [firstPair]

private def lastPair (f : Coefficient) :
    ((Quark ⊗[ℂ] Quark) ⊗[ℂ] (Quark ⊗[ℂ] Quark)) →ₗ[ℂ]
      (Quark ⊗[ℂ] Quark) →ₗ[ℂ] ℂ where
  toFun p := TensorProduct.lift (TensorProduct.lift (secondPair f) p)
  map_add' p q := by ext x y; simp
  map_smul' z p := by ext x y; simp

def orderedLift (f : Coefficient) : SixSlotAlternation.OrderedSpace Quark Quark →ₗ[ℂ] ℂ :=
  TensorProduct.lift (lastPair f)

@[simp] theorem orderedLift_apply (f : Coefficient) (a b c d e x : Quark) :
    orderedLift f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] x)) =
      f ![a,b,c,d,e,x] := by
  simp only [orderedLift, lastPair, secondPair, firstPair, TensorProduct.lift.tmul,
    LinearMap.coe_mk, AddHom.coe_mk, curried, MultilinearMap.curryRight_apply]
  congr 1
  ext i; fin_cases i <;> rfl

attribute [local irreducible] orderedLift

private theorem physical_fields (g : DeltaBTwoSixQuark.SymmetryGroup) :
    DeltaBTwoSixQuark.upField g = StandardSMGaugeTensor.phase 4 g.1 •
      (colorAction g.1.1).comp (spinAction g.2) ∧
    DeltaBTwoSixQuark.downField g = StandardSMGaugeTensor.phase (-2) g.1 •
      (colorAction g.1.1).comp (spinAction g.2) := by
  constructor <;> apply TensorProduct.ext <;> ext a s <;>
    simp [DeltaBTwoSixQuark.upField, DeltaBTwoSixQuark.downField,
      ExternalInvariantTensor.external, StandardSMGaugeTensor.upRight,
      StandardSMGaugeTensor.downRight, StandardSMGaugeTensor.twist,
      StandardSMGaugeTensor.color, colorAction, spinAction,
      SmallSpecialUnitary.defining, TensorProduct.smul_tmul]

def orderedIntertwiner (f : Coefficient) (hf : IsInvariant f) :
    IntertwiningMap (SixSlotAlternation.orderedRepresentation
      DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField)
      (Representation.trivial ℂ DeltaBTwoSixQuark.SymmetryGroup ℂ) where
  toLinearMap := orderedLift f
  isIntertwining' g := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro b
    apply TensorProduct.ext
    apply LinearMap.ext; intro c
    apply LinearMap.ext; intro d
    apply TensorProduct.ext
    apply LinearMap.ext; intro e
    apply LinearMap.ext; intro x
    change orderedLift f (((DeltaBTwoSixQuark.upField g a ⊗ₜ[ℂ]
      DeltaBTwoSixQuark.downField g b) ⊗ₜ[ℂ] (DeltaBTwoSixQuark.upField g c ⊗ₜ[ℂ]
      DeltaBTwoSixQuark.downField g d)) ⊗ₜ[ℂ] (DeltaBTwoSixQuark.downField g e ⊗ₜ[ℂ]
      DeltaBTwoSixQuark.downField g x)) =
        orderedLift f (((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] d)) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] x))
    rw [orderedLift_apply, orderedLift_apply]
    rw [(physical_fields g).1, (physical_fields g).2]
    let z : Fin 6 → ℂ := ![StandardSMGaugeTensor.phase 4 g.1,
      StandardSMGaugeTensor.phase (-2) g.1, StandardSMGaugeTensor.phase 4 g.1,
      StandardSMGaugeTensor.phase (-2) g.1, StandardSMGaugeTensor.phase (-2) g.1,
      StandardSMGaugeTensor.phase (-2) g.1]
    let v : Fin 6 → Quark := ![a,b,c,d,e,x]
    have hact : f (fun i => z i • colorAction g.1.1 (spinAction g.2 (v i))) = f v := by
      rw [f.map_smul_univ, hf.1, hf.2]
      have hz : ∏ i, z i = 1 := by
        simpa [z, Fin.prod_univ_succ, mul_assoc] using DeltaBTwoSixQuark.sixQuark_phases g.1
      rw [hz, one_smul]
    convert hact using 1
    congr 1
    ext i; fin_cases i <;> rfl

attribute [local irreducible] orderedIntertwiner
attribute [local irreducible] DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField

@[simp] theorem orderedIntertwiner_toLinearMap (f : Coefficient) (hf : IsInvariant f) :
    (orderedIntertwiner f hf).toLinearMap = orderedLift f := by
  unfold orderedIntertwiner; rfl

abbrev Sector := SixSlotSpeciesDegree.sector
  DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField

def liftCoefficient (f : admissible) : Sector :=
  ⟨(1 / 48 : ℂ) • SixSlotAlternation.coefficient
    DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField
      (orderedIntertwiner f.1 f.2.1),
    (SixSlotSpeciesDegree.sector _ _).smul_mem _
      (SixSlotSpeciesDegree.coefficient_hasDegree _ _ _)⟩

attribute [local irreducible] liftCoefficient

private theorem pattern_membership :
    ∀ p : Equiv.Perm (Fin 6), SixSlotAlternation.PreservesPattern p →
      ∀ i, (p i = 0 ∨ p i = 2) ↔ (i = 0 ∨ i = 2) := by decide +kernel

theorem restriction_liftCoefficient (f : admissible) :
    exteriorRestriction (liftCoefficient f).1 = f.1 := by
  ext v
  rw [exteriorRestriction_apply]
  unfold liftCoefficient
  rw [IntertwiningMap.smul_apply, SixSlotAlternation.coefficient_apply_ιMulti,
    orderedIntertwiner_toLinearMap]
  have he : SixSlotAlternation.alternating (orderedLift f.1)
      (SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)) = 48 • f.1 v := by
    convert SixSlotAlternation.alternating_slots_of_preserves (orderedLift f.1)
      (v 0) (v 2) (v 1) (v 3) (v 4) (v 5) ?_ using 1
    · simp only [orderedLift_apply]; congr 2; ext i; fin_cases i <;> rfl
    · intro p hp
      have hv : ![((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 0)).1), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 1)).2), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 2)).1), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 3)).2), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 4)).2), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 5)).2)] = v ∘ p := by
        ext i
        have hm := pattern_membership p hp i
        fin_cases i <;> generalize hk : p _ = k at * <;>
          fin_cases k <;> simp [SixSlotAlternation.slots, hk] at *
        all_goals rw [hk]
      simp only [SixSlotAlternation.ordered, MultilinearMap.mk'_apply,
        Function.comp_apply, orderedLift_apply]
      change f.1 ![((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 0)).1), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 1)).2), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 2)).1), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 3)).2), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 4)).2), ((SixSlotAlternation.slots (v 0) (v 2) (v 1) (v 3) (v 4) (v 5)
          (p 5)).2)] = _
      rw [hv]
      have hvec : ![v 0, v 1, v 2, v 3, v 4, v 5] = v := by
        ext i; fin_cases i <;> rfl
      rw [hvec]
      exact f.2.2 p hp v
  rw [he]
  simp [smul_eq_mul]

def restrictSector (f : Sector) : admissible :=
  ⟨exteriorRestriction f.1, orderedCoefficient_invariant _,
    exteriorRestriction_speciesAlternating _⟩

theorem liftCoefficient_restrictSector (f : Sector) :
    liftCoefficient (restrictSector f) = f := by
  apply Subtype.ext
  apply SixSlotSpeciesRestriction.slots_ext _ _ _ _
    (liftCoefficient (restrictSector f)).2 f.2
  intro a c b d e x
  have he := congrArg (fun F : Coefficient => F ![a,b,c,d,e,x])
    (restriction_liftCoefficient (restrictSector f))
  simpa [restrictSector, exteriorRestriction_apply] using he

def restrictionEquiv : Sector ≃ₗ[ℂ] admissible where
  toFun := restrictSector
  invFun := liftCoefficient
  left_inv := liftCoefficient_restrictSector
  right_inv f := Subtype.ext (restriction_liftCoefficient f)
  map_add' f h := by
    apply Subtype.ext
    ext v
    simp only [restrictSector, exteriorRestriction_apply]
    rfl
  map_smul' z f := by
    apply Subtype.ext
    ext v
    simp only [restrictSector, exteriorRestriction_apply]
    rfl

/-- Intrinsic completeness: two evaluations classify the whole degree `(2,4)`
invariant exterior sector, not a contraction-generated subspace. -/
def twoCoordinateEquiv : Sector ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  restrictionEquiv.trans coefficientProbeEquiv

theorem twoCoordinateEquiv_apply (f : Sector) :
    twoCoordinateEquiv f = twoProbes (exteriorRestriction f.1) := rfl

theorem twoCoordinateEquiv_symm_apply (t : Fin 2 → ℂ) :
    twoCoordinateEquiv.symm t = liftCoefficient (fromProbesCoefficient t) := rfl

theorem finrank_sector : Module.finrank ℂ Sector = 2 := by
  rw [twoCoordinateEquiv.finrank_eq]
  simp

theorem probes_inverse (t : Fin 2 → ℂ) :
    twoProbes (exteriorRestriction (liftCoefficient (fromProbesCoefficient t)).1) = t := by
  rw [restriction_liftCoefficient]
  exact probes_fromProbes t

theorem inverse_probes (f : Sector) :
    liftCoefficient (fromProbesCoefficient (twoProbes (exteriorRestriction f.1))) = f :=
  twoCoordinateEquiv.symm_apply_apply f

end
end Physics.SixQuarkTwoCoordinates
