import GUT.SU6.Yukawa.BlockCoordinates
import TauCeti.RepresentationTheory.Irreducible

open Physics

open Math

/-! The singlet kernel is a genuine trivial residual subrepresentation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GUT.SU6YukawaSinglets
noncomputable section
open StandardSMUVFields StandardSMUVStabilizer SU6YukawaLight SU6FiveCouplings

theorem standard_last (g : StandardSMGaugeTensor.GaugeGroup) (x : Six) :
    FundamentalRepresentation.rho (StandardSMGroup.hom g) x 5 = x 5 :=
  congrArg (fun y : StandardSMFullGaugeMass.Heavy => y.2.2)
    (StandardSMGroup.splitEquiv_action g x)

theorem dualProbe_fixed (g : StandardSMGaugeTensor.GaugeGroup) :
    ConcreteSU6Representations.antifundamental.rho (StandardSMGroup.hom g) (dualProbe 5) =
      dualProbe 5 := by
  apply dualCoordinates.toLinearEquiv.injective
  change dualCoordinates
      (ConcreteSU6Representations.antifundamental.rho (StandardSMGroup.hom g) (dualProbe 5)) =
    dualCoordinates (dualProbe 5)
  apply LinearMap.ext
  intro x
  rw [dualCoordinates_action, dualProbe_apply, dualProbe_apply, ← map_inv]
  exact standard_last g⁻¹ x

theorem pureSinglet_fixed (H : Type*) [CommGroup H]
    (g : StandardSMGaugeTensor.GaugeGroup × H) (s t : ℂ) :
    StandardSMUVMass.rho H g (pureSinglet s t) = pureSinglet s t := by
  change ((ConcreteSU6Representations.exteriorTwo.rho (StandardSMGroup.hom g.1) 0,
    ConcreteSU6Representations.antifundamental.rho (StandardSMGroup.hom g.1) (s • dualProbe 5)),
    ConcreteSU6Representations.antifundamental.rho (StandardSMGroup.hom g.1) (t • dualProbe 5)) = _
  simp only [map_zero, map_smul, dualProbe_fixed, pureSinglet]

def lift : (Fin 2 → ℂ) →ₗ[ℂ] UV where
  toFun x := pureSinglet (x 0) (x 1)
  map_add' x y := by simp [pureSinglet, add_smul]
  map_smul' c x := by simp [pureSinglet, mul_smul]

theorem lift_injective : Function.Injective lift := by
  intro x y h
  have hf := congrArg (fun z => fcoord z 5) h
  have hg := congrArg (fun z => gcoord z 5) h
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, fcoord, gcoord, pureSinglet,
    map_smul, LinearMap.smul_apply, dualProbe_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at hf hg
  funext i
  fin_cases i
  · exact hf
  · exact hg

theorem singlet_kernel_iff (u v w : ℂ) (x : Fin 2 → ℂ) :
    x ∈ (SmallSymmetricRank.singlet u v w).mulVecLin.ker ↔
      u * x 0 + v * x 1 = 0 ∧ v * x 0 + w * x 1 = 0 := by
  simp [LinearMap.mem_ker, SmallSymmetricRank.singlet,
    funext_iff, Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]

abbrev Kernel (u v w : ℂ) := (SmallSymmetricRank.singlet u v w).mulVecLin.ker

def embedding (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    Representation.IntertwiningMap
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) (Kernel u v w))
      (mass H a b u v w).radical.toRepresentation where
  toLinearMap := {
    toFun x := ⟨lift x.val, (pureSinglet_light_iff H a b u v w _ _).mpr
      ((singlet_kernel_iff u v w x.val).mp x.property)⟩
    map_add' x y := Subtype.ext (lift.map_add x.val y.val)
    map_smul' c x := Subtype.ext (lift.map_smul c x.val) }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (pureSinglet_fixed H g (x.val 0) (x.val 1)).symm

theorem embedding_injective (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    Function.Injective (embedding H a b u v w) := by
  intro x y h
  apply Subtype.ext
  exact lift_injective (congrArg Subtype.val h)

theorem singlet_dimension (u v w : ℂ) :
    Module.finrank ℂ (Kernel u v w) =
      2 - (if u = 0 ∧ v = 0 ∧ w = 0 then 0 else if u * w - v * v = 0 then 1 else 2) := by
  rw [SmallSymmetricRank.matrix_nullity, SmallSymmetricRank.singlet_rank]

theorem standard_sixth (g : StandardSMGaugeTensor.GaugeGroup) :
    FundamentalRepresentation.rho (StandardSMGroup.hom g) sixth = sixth := by
  apply StandardSMGroup.splitEquiv.injective
  rw [StandardSMGroup.splitEquiv_action]
  have hs : StandardSMGroup.splitEquiv sixth = (0, (0, 1)) := by
    simp [StandardSMGroup.splitEquiv, sixth]
  rw [hs]
  change (_, (_, (1 : ℂ))) = (0, (0, 1))
  simp

theorem singlet_coordinates_fixed (H : Type*) [CommGroup H]
    (g : StandardSMGaugeTensor.GaugeGroup × H) (x : UV) :
    fcoord (StandardSMUVMass.rho H g x) 5 = fcoord x 5 ∧
    gcoord (StandardSMUVMass.rho H g x) 5 = gcoord x 5 := by
  change dualCoordinates (ConcreteSU6Representations.antifundamental.rho
        (StandardSMGroup.hom g.1) x.1.2) (Pi.single 5 1) = _ ∧
    dualCoordinates (ConcreteSU6Representations.antifundamental.rho
        (StandardSMGroup.hom g.1) x.2) (Pi.single 5 1) = _
  simp only [dualCoordinates_action, ← map_inv, single_five, standard_sixth]
  simp only [fcoord, gcoord, single_five, and_self]

def projection (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    Representation.IntertwiningMap (mass H a b u v w).radical.toRepresentation
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) (Kernel u v w)) where
  toLinearMap := {
    toFun x := ⟨![fcoord x.val 5, gcoord x.val 5], by
      rw [singlet_kernel_iff]
      exact ((radical_iff H a b u v w x.val).mp x.property).2⟩
    map_add' x y := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact (fMap 5).map_add x.val y.val
      · exact (gMap 5).map_add x.val y.val
    map_smul' c x := by
      apply Subtype.ext
      funext i
      fin_cases i
      · exact (fMap 5).map_smul c x.val
      · exact (gMap 5).map_smul c x.val }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext i
    fin_cases i
    · exact (singlet_coordinates_fixed H g x.val).1
    · exact (singlet_coordinates_fixed H g x.val).2

def singletSplit (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    SplitRepresentationProjection.Split (mass H a b u v w).radical.toRepresentation
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) (Kernel u v w)) where
  project := projection H a b u v w
  embed := embedding H a b u v w
  left_inv x := by
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [projection, embedding, lift, pureSinglet, fcoord, gcoord, dualProbe_apply]

def trivialCopiesEquiv (H : Type*) [CommGroup H] (u v w : ℂ) :
    Representation.Equiv
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) (Kernel u v w))
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H)
        (Fin (Module.finrank ℂ (Kernel u v w)) → ℂ)) :=
  Representation.Equiv.mk (Module.finBasis ℂ (Kernel u v w)).equivFun (by
    intro g
    apply LinearMap.ext
    intro x
    rfl)

theorem scalar_irreducible (H : Type*) [CommGroup H] :
    (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) ℂ).IsIrreducible :=
  inferInstance

def trivialCopiesSplit (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    SplitRepresentationProjection.Split (mass H a b u v w).radical.toRepresentation
      (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H)
        (Fin (Module.finrank ℂ (Kernel u v w)) → ℂ)) :=
  (singletSplit H a b u v w).trans
    (SplitRepresentationProjection.Split.ofEquiv (trivialCopiesEquiv H u v w))

theorem projection_surjective (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    Function.Surjective (projection H a b u v w) := by
  intro x
  exact ⟨embedding H a b u v w x, (singletSplit H a b u v w).left_inv x⟩

theorem complement_dimension (H : Type*) [CommGroup H] (a b u v w : ℂ) :
    Module.finrank ℂ (projection H a b u v w).toLinearMap.ker =
      if a = 0 ∧ b = 0 then 25 else 15 := by
  have h := LinearMap.finrank_range_add_finrank_ker (projection H a b u v w).toLinearMap
  rw [LinearMap.range_eq_top.mpr (projection_surjective H a b u v w),
    finrank_top, singlet_dimension, SU6YukawaCoordinates.radical_finrank] at h
  split_ifs at h ⊢ <;> omega

end
end GUT.SU6YukawaSinglets
