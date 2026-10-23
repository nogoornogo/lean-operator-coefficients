import GUT.SU6.Branching.StandardU5Group
import GUT.SU6.Branching.SU5TorusCompatibility

open Physics

/-! The existing concrete U(5) block embedding restricts to the standard
SU(5) subgroup and factors the legacy (-2,3) physical torus map. -/

set_option autoImplicit false

namespace GUT.SU6.StandardSU5Inclusion

noncomputable section

open SU5.StandardModelEmbedding SU5TorusCompatibility

def toU5 : TargetGroup →* StandardU5Group.U5 where
  toFun A := ⟨A.val, A.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def inclusion : TargetGroup →* ActualRestriction.SU6 := StandardU5Group.embedding.comp toU5

theorem inclusion_injective : Function.Injective inclusion := by
  intro a b he
  exact Subtype.ext (congrArg (fun A : StandardU5Group.U5 => A.val)
    (StandardU5Group.embedding_injective he))

set_option maxRecDepth 2000 in
theorem inclusion_continuous : Continuous inclusion := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun A : TargetGroup =>
    StandardU5Group.rawEmbeddingMatrix (toU5 A)
      (StandardU5Group.blockIndexEquiv.symm i) (StandardU5Group.blockIndexEquiv.symm j))
  unfold StandardU5Group.rawEmbeddingMatrix
  cases hi : StandardU5Group.blockIndexEquiv.symm i with
  | inl a =>
    cases hj : StandardU5Group.blockIndexEquiv.symm j with
    | inl b =>
      change Continuous (fun A : TargetGroup => A.val a b)
      exact (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)
    | inr b => exact continuous_const
  | inr a =>
    cases hj : StandardU5Group.blockIndexEquiv.symm j with
    | inl b => exact continuous_const
    | inr b =>
      have hd (A : TargetGroup) : Matrix.det (toU5 A).val = 1 := A.property.2
      simp only [StandardU5Group.singletBlock, hd, star_one]
      exact continuous_const

theorem physical_coord (x : PhysicalSMTorusTarget.Group) (i : Fin 5) :
    (PhysicalTorusCharacterBridge.physicalDiagonalPoint (-2) 3 x.toAdd).coords i.castSucc =
      (AddCircle.toCircle (PhysicalTorusCharacterBridge.ambientTorusPoint (-2) 3 x.toAdd i) : ℂ) := by
  fin_cases i <;> rfl

theorem physical_entries (x : PhysicalSMTorusTarget.Group) (i : Fin 5) :
    (SU5.PhysicalTorus.entries (circleCoordinates x) i : ℂ) =
      (AddCircle.toCircle (PhysicalTorusCharacterBridge.ambientTorusPoint (-2) 3 x.toAdd i) : ℂ) := by
  apply congrArg (fun z : Circle => (z : ℂ))
  fin_cases i
  · change AddCircle.toCircle (x.toAdd 0) * AddCircle.toCircle (x.toAdd 3) ^ (-2 : ℤ) =
      AddCircle.toCircle (x.toAdd 0 + (-2 : ℤ) • x.toAdd 3)
    rw [AddCircle.toCircle_add, AddCircle.toCircle_zsmul]
  · change AddCircle.toCircle (x.toAdd 1) * AddCircle.toCircle (x.toAdd 3) ^ (-2 : ℤ) =
      AddCircle.toCircle (x.toAdd 1 + (-2 : ℤ) • x.toAdd 3)
    rw [AddCircle.toCircle_add, AddCircle.toCircle_zsmul]
  · change (AddCircle.toCircle (x.toAdd 0) * AddCircle.toCircle (x.toAdd 1))⁻¹ *
      AddCircle.toCircle (x.toAdd 3) ^ (-2 : ℤ) =
      AddCircle.toCircle (-x.toAdd 0 - x.toAdd 1 + (-2 : ℤ) • x.toAdd 3)
    rw [sub_eq_add_neg, AddCircle.toCircle_add, AddCircle.toCircle_add,
      AddCircle.toCircle_neg, AddCircle.toCircle_neg, AddCircle.toCircle_zsmul]
    simp only [mul_inv_rev]
    ac_rfl
  · change AddCircle.toCircle (x.toAdd 2) * AddCircle.toCircle (x.toAdd 3) ^ (3 : ℤ) =
      AddCircle.toCircle (x.toAdd 2 + (3 : ℤ) • x.toAdd 3)
    rw [AddCircle.toCircle_add, AddCircle.toCircle_zsmul]
  · change (AddCircle.toCircle (x.toAdd 2))⁻¹ * AddCircle.toCircle (x.toAdd 3) ^ (3 : ℤ) =
      AddCircle.toCircle (-x.toAdd 2 + (3 : ℤ) • x.toAdd 3)
    rw [AddCircle.toCircle_add, AddCircle.toCircle_neg, AddCircle.toCircle_zsmul]

theorem torus_toU5 (x : PhysicalSMTorusTarget.Group) :
    toU5 (SU5.MaximalTorus.hom (torusCover x)) =
      StandardU5Group.torusPoint (PhysicalTorusCharacterBridge.physicalDiagonalPoint (-2) 3 x.toAdd) := by
  apply Subtype.ext
  change Matrix.diagonal (fun i => (SU5.PhysicalTorus.entries (circleCoordinates x) i : ℂ)) =
    Matrix.diagonal (fun i : Fin 5 =>
      (PhysicalTorusCharacterBridge.physicalDiagonalPoint (-2) 3 x.toAdd).coords i.castSucc)
  apply congrArg Matrix.diagonal
  funext i
  rw [physical_coord, physical_entries]

theorem inclusion_torus (x : PhysicalSMTorusTarget.Group) :
    inclusion (SU5.MaximalTorus.hom (torusCover x)) = PhysicalSMTorusTarget.embedding (-2) 3 x := by
  rw [inclusion, MonoidHom.comp_apply, torus_toU5, StandardU5Group.embedding_torusPoint]
  exact (PhysicalSMTorusTarget.embedding_ofAdd (-2) 3 x.toAdd).symm

end

end GUT.SU6.StandardSU5Inclusion
