import Physics.StandardModel.Operators.SixQuarkFlavorResidualHom

open Math

/-! Typed within-species exchanges for different up/down multiplicity spaces.
No equivalence between the two species is assumed. -/
namespace GUT.SixQuarkTypedFlavor
set_option autoImplicit false
noncomputable section
open SixQuarkFlavorCoordinates SixQuarkSpeciesQuotient
open SixQuarkFlavorResidualHom
open scoped TensorProduct

universe u
variable (U D : Type u) [AddCommGroup U] [Module ℂ U]
  [AddCommGroup D] [Module ℂ D]

def Flavor (b : Bool) : Type u := match b with | true => U | false => D
attribute [reducible] Flavor

instance flavorAddCommGroup (b : Bool) : AddCommGroup (Flavor U D b) :=
  match b with | true => inferInstanceAs (AddCommGroup U) | false => inferInstanceAs (AddCommGroup D)

instance flavorModule (b : Bool) : Module ℂ (Flavor U D b) :=
  match b with | true => inferInstanceAs (Module ℂ U) | false => inferInstanceAs (Module ℂ D)

instance flavorFiniteDimensional [FiniteDimensional ℂ U] [FiniteDimensional ℂ D]
    (b : Bool) : FiniteDimensional ℂ (Flavor U D b) :=
  match b with | true => inferInstanceAs (FiniteDimensional ℂ U)
               | false => inferInstanceAs (FiniteDimensional ℂ D)

/-- The ordered `(up,down,up,down,down,down)` flavor family. -/
abbrev SlotFlavor (i : Fin 6) := Flavor U D (decide (i = 0 ∨ i = 2))

/-- Each generator exchanges equal fibers; none exchanges `U` with `D`. -/
def speciesExchange (g : Fin 4) : TypedExchange (V := SlotFlavor U D) g := by
  intro i
  have hp : decide (slotSwap g i = 0 ∨ slotSwap g i = 2) = decide (i = 0 ∨ i = 2) := by
    fin_cases g <;> fin_cases i <;> decide
  have transport (a b : Bool) (h : a = b) : Flavor U D a ≃ₗ[ℂ] Flavor U D b := by
    cases h
    exact LinearEquiv.refl ℂ _
  exact transport _ _ hp

def tensorExchange (g : Fin 4) (i : Fin 6) :
    SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D (slotSwap g i) ≃ₗ[ℂ]
      SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D i :=
  TensorProduct.congr (LinearEquiv.refl ℂ _) (speciesExchange U D g i)

/-- The dependent reindexing is bundled as a multilinear map. -/
def swapCoefficient (g : Fin 4) (f : FlavorCoefficient (V := SlotFlavor U D)) :
    FlavorCoefficient (V := SlotFlavor U D) := match g with
  | 0 =>
    ((MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ
      (fun i => SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D i) ℂ
      (slotSwap 0)) f).compLinearMap (fun i => (tensorExchange U D 0 i).symm.toLinearMap)
  | 1 =>
    ((MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ
      (fun i => SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D i) ℂ
      (slotSwap 1)) f).compLinearMap (fun i => (tensorExchange U D 1 i).symm.toLinearMap)
  | 2 =>
    ((MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ
      (fun i => SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D i) ℂ
      (slotSwap 2)) f).compLinearMap (fun i => (tensorExchange U D 2 i).symm.toLinearMap)
  | 3 =>
    ((MultilinearMap.domDomCongrLinearEquiv' ℂ ℂ
      (fun i => SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D i) ℂ
      (slotSwap 3)) f).compLinearMap (fun i => (tensorExchange U D 3 i).symm.toLinearMap)

theorem swapCoefficient_apply (g : Fin 4) (f : FlavorCoefficient (V := SlotFlavor U D))
    (v : ∀ i, SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D i) :
    swapCoefficient U D g f v = f (fun i => tensorExchange U D g i (v (slotSwap g i))) := by
  fin_cases g
  all_goals unfold swapCoefficient
  all_goals apply congrArg f
  all_goals funext i; fin_cases i
  all_goals rfl

theorem typed_swap_full (f : FlavorCoefficient (V := SlotFlavor U D))
    (hf : IsTypedSwapAlternating (speciesExchange U D) f) (g : Fin 4)
    (v : ∀ i, SixQuarkInvariant.Quark ⊗[ℂ] SlotFlavor U D i) :
    f (fun i => tensorExchange U D g i (v (slotSwap g i))) = -f v := by
  have he : swapCoefficient U D g f = -f := by
    apply pure_ext
    intro q t
    rw [swapCoefficient_apply]
    simpa [tensorExchange, exchangeFlavor] using hf g q t
  simpa only [swapCoefficient_apply, neg_apply] using DFunLike.congr_fun he v

theorem statistics_iff (f : FlavorCoefficient (V := SlotFlavor U D))
    (hf : IsInvariant f) :
    IsTypedSwapAlternating (speciesExchange U D) f ↔
      SatisfiesTypedStatistics (speciesExchange U D) (flavorCoordinates f) :=
  typed_statistics_iff _ f hf

variable {H : Type*} [Group H]
  (up : Representation ℂ H U) (down : Representation ℂ H D)

def flavorRepresentation (b : Bool) : Representation ℂ H (Flavor U D b) :=
  match b with | true => up | false => down

abbrev slotRepresentation (i : Fin 6) :=
  flavorRepresentation U D up down (decide (i = 0 ∨ i = 2))

/-- Independently specified heterogeneous flavored coefficients. -/
abbrev coefficientSubmodule : Submodule ℂ (FlavorCoefficient (V := SlotFlavor U D)) where
  carrier := {f | IsInvariant f ∧ IsResidualInvariant (slotRepresentation U D up down) f ∧
    IsTypedSwapAlternating (speciesExchange U D) f}
  zero_mem' := by simp [IsInvariant, IsResidualInvariant, IsTypedSwapAlternating]
  add_mem' := by
    intro f k hf hk
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro g v; change f _ + k _ = f v + k v; rw [hf.1.1, hk.1.1]
    · intro g v; change f _ + k _ = f v + k v; rw [hf.1.2, hk.1.2]
    · intro g v; change f _ + k _ = f v + k v; rw [hf.2.1, hk.2.1]
    · intro g q t
      change f _ + k _ = -(f _ + k _)
      rw [hf.2.2, hk.2.2, neg_add]
  smul_mem' := by
    intro z f hf
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro g v; change z • f _ = z • f v; rw [hf.1.1]
    · intro g v; change z • f _ = z • f v; rw [hf.1.2]
    · intro g v; change z • f _ = z • f v; rw [hf.2.1]
    · intro g q t
      change z • f _ = -(z • f _)
      rw [hf.2.2, smul_neg]

abbrev Coefficients := ↥(coefficientSubmodule U D up down)

/-- The residual Hom with genuinely typed up/down exchange equations. -/
abbrev statisticsSubmodule : Submodule ℂ (Hom (slotRepresentation U D up down)) where
  carrier := {k | SatisfiesTypedStatistics (speciesExchange U D)
    (fun t => homCoordinates (slotRepresentation U D up down) k t)}
  zero_mem' := by
    intro g t
    ext p q
    simp [homCoordinates, MultilinearInvariantHom.toMultilinear, transform]
  add_mem' := by
    intro k l hk hl g t
    ext p q
    have h := congrArg₂ (· + ·) (congrFun (congrFun (hk g t) p) q)
      (congrFun (congrFun (hl g t) p) q)
    simp [homCoordinates, MultilinearInvariantHom.toMultilinear, transform,
      mul_add, Finset.sum_add_distrib] at h ⊢
    linear_combination h
  smul_mem' := by
    intro z k hk g t
    ext p q
    have h := congrArg (z * ·) (congrFun (congrFun (hk g t) p) q)
    simpa [homCoordinates, MultilinearInvariantHom.toMultilinear, transform,
      smul_eq_mul, Finset.mul_sum, mul_left_comm, mul_assoc] using h

abbrev StatisticsHom := ↥(statisticsSubmodule U D up down)


def toHom (f : Coefficients U D up down) : StatisticsHom U D up down := by
  refine ⟨residualHom _ f.val f.property.1 f.property.2.1, ?_⟩
  change SatisfiesTypedStatistics (speciesExchange U D)
    (fun t => homCoordinates _ (residualHom _ f.val f.property.1 f.property.2.1) t)
  simp only [homCoordinates_residualHom, flavorCoordinatesMap_apply]
  exact (statistics_iff U D f.val f.property.1).mp f.property.2.2

def fromHom (k : StatisticsHom U D up down) : Coefficients U D up down := by
  refine ⟨assembleHom _ k.val, assembleHom_invariant _ k.val,
    assembleHom_residualInvariant _ k.val, ?_⟩
  apply (statistics_iff U D _ (assembleHom_invariant _ k.val)).mpr
  change SatisfiesTypedStatistics (speciesExchange U D)
    (flavorCoordinates (assemble (homCoordinates _ k.val)))
  rw [coordinates_assemble]
  exact k.property

def homEquiv : Coefficients U D up down ≃ StatisticsHom U D up down where
  toFun := toHom U D up down
  invFun := fromHom U D up down
  left_inv f := by
    apply Subtype.ext
    exact assembleHom_residualHom _ f.val f.property.1 f.property.2.1
  right_inv k := by
    apply Subtype.ext
    exact residualHom_assembleHom _ k.val

def homLinearEquiv : Coefficients U D up down ≃ₗ[ℂ] StatisticsHom U D up down :=
  { homEquiv U D up down with
    map_add' := by
      intro f k
      apply Subtype.ext
      apply Representation.IntertwiningMap.ext
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro t
      change PiTensorProduct.lift (flavorCoordinatesMap (f + k).val)
        (PiTensorProduct.tprod ℂ t) =
          PiTensorProduct.lift (flavorCoordinatesMap f.val) (PiTensorProduct.tprod ℂ t) +
            PiTensorProduct.lift (flavorCoordinatesMap k.val) (PiTensorProduct.tprod ℂ t)
      simp only [PiTensorProduct.lift.tprod, flavorCoordinatesMap_apply]
      change coordinateLinear (fixedFlavor (f.val + k.val) t) =
        coordinateLinear (fixedFlavor f.val t) + coordinateLinear (fixedFlavor k.val t)
      have he : fixedFlavor (f.val + k.val) t = fixedFlavor f.val t + fixedFlavor k.val t := by
        ext q; rfl
      rw [he, map_add]
    map_smul' := by
      intro z f
      apply Subtype.ext
      apply Representation.IntertwiningMap.ext
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro t
      change PiTensorProduct.lift (flavorCoordinatesMap (z • f).val)
        (PiTensorProduct.tprod ℂ t) =
          z • PiTensorProduct.lift (flavorCoordinatesMap f.val) (PiTensorProduct.tprod ℂ t)
      simp only [PiTensorProduct.lift.tprod, flavorCoordinatesMap_apply]
      change coordinateLinear (fixedFlavor (z • f.val) t) =
        z • coordinateLinear (fixedFlavor f.val t)
      have he : fixedFlavor (z • f.val) t = z • fixedFlavor f.val t := by
        ext q; rfl
      rw [he, map_smul] }

theorem exists_nonzero_iff :
    (∃ f : Coefficients U D up down, f ≠ 0) ↔
      ∃ k : StatisticsHom U D up down, k ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨homLinearEquiv U D up down f,
      fun h => hf ((homLinearEquiv U D up down).map_eq_zero_iff.mp h)⟩
  · rintro ⟨k, hk⟩
    exact ⟨(homLinearEquiv U D up down).symm k,
      fun h => hk ((homLinearEquiv U D up down).symm.map_eq_zero_iff.mp h)⟩

/-- The common pointwise statistics proof leaves global Hom extraction and
assembly unchanged, with genuinely different up/down flavor carriers. -/
@[simp] theorem homLinearEquiv_apply (f : Coefficients U D up down) :
    (homLinearEquiv U D up down f).val =
      residualHom _ f.val f.property.1 f.property.2.1 := rfl

@[simp] theorem homLinearEquiv_symm_apply (k : StatisticsHom U D up down) :
    ((homLinearEquiv U D up down).symm k).val = assembleHom _ k.val := rfl

end
end GUT.SixQuarkTypedFlavor
