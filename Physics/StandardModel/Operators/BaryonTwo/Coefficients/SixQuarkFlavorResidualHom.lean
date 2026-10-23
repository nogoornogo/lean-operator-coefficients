import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFlavorCoordinates
import Math.RepresentationTheory.Invariants.MultilinearInvariantHom

open Math

/-! Residual Hom coordinates for flavored six-quark tensors. Exchange equations
remain explicit on this Hom; no Schur-functor decomposition is assumed. -/
namespace Physics.SixQuarkFlavorResidualHom
set_option autoImplicit false
noncomputable section
open Representation SixQuarkFlavorCoordinates
open scoped TensorProduct

variable {H : Type*} [Group H]
  {V : Fin 6 → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (r : ∀ i, Representation ℂ H (V i))

abbrev Hom := IntertwiningMap (MultilinearInvariantHom.tensorRepresentation r)
  (Representation.trivial ℂ H (Fin 5 → Fin 5 → ℂ))

def homCoordinates (k : Hom r) : MultilinearMap ℂ V (Fin 5 → Fin 5 → ℂ) :=
  (MultilinearInvariantHom.toMultilinear r k).val

def residualHom (f : FlavorCoefficient (V := V)) (hf : IsInvariant f)
    (hr : IsResidualInvariant r f) : Hom r :=
  MultilinearInvariantHom.fromMultilinear r
    ⟨flavorCoordinatesMap f, (residual_invariance_iff r f hf).mp hr⟩

theorem homCoordinates_residualHom (f : FlavorCoefficient (V := V))
    (hf : IsInvariant f) (hr : IsResidualInvariant r f) :
    homCoordinates r (residualHom r f hf hr) = flavorCoordinatesMap f := by
  apply MultilinearMap.ext
  intro t
  change PiTensorProduct.lift (flavorCoordinatesMap f) (PiTensorProduct.tprod ℂ t) =
    flavorCoordinatesMap f t
  exact PiTensorProduct.lift.tprod _


def assembleHom (k : Hom r) : FlavorCoefficient (V := V) :=
  assemble (homCoordinates r k)

theorem assembleHom_invariant (k : Hom r) : IsInvariant (assembleHom r k) :=
  assemble_invariant _

theorem assembleHom_residualInvariant (k : Hom r) :
    IsResidualInvariant r (assembleHom r k) := by
  apply (residual_invariance_iff r _ (assembleHom_invariant r k)).mpr
  intro g t
  change flavorCoordinates (assemble (homCoordinates r k)) (fun i => r i g (t i)) =
    flavorCoordinates (assemble (homCoordinates r k)) t
  rw [coordinates_assemble]
  exact (MultilinearInvariantHom.toMultilinear r k).property g t

theorem assembleHom_residualHom (f : FlavorCoefficient (V := V))
    (hf : IsInvariant f) (hr : IsResidualInvariant r f) :
    assembleHom r (residualHom r f hf hr) = f := by
  rw [assembleHom, homCoordinates_residualHom, assemble_coordinates f hf]

theorem residualHom_assembleHom (k : Hom r) :
    residualHom r (assembleHom r k) (assembleHom_invariant r k)
      (assembleHom_residualInvariant r k) = k := by
  apply IntertwiningMap.ext
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro t
  change PiTensorProduct.lift (flavorCoordinatesMap (assembleHom r k))
    (PiTensorProduct.tprod ℂ t) = k (PiTensorProduct.tprod ℂ t)
  rw [PiTensorProduct.lift.tprod, flavorCoordinatesMap_apply]
  change flavorCoordinates (assemble (homCoordinates r k)) t = _
  rw [coordinates_assemble]
  rfl

section Statistics
variable {F : Type*} [AddCommGroup F] [Module ℂ F]
  (s : Fin 6 → Representation ℂ H F)

/-- Full within-species alternation on the flavored tensor slots. -/
abbrev coefficientSubmodule : Submodule ℂ (FlavorCoefficient (V := fun _ => F)) where
  carrier := {f | IsInvariant f ∧ IsResidualInvariant s f ∧ IsSpeciesAlternating f}
  zero_mem' := by
    simp [IsInvariant, IsResidualInvariant, IsSpeciesAlternating]
  add_mem' := by
    intro f g hf hg
    constructor
    · constructor
      · intro a v; change f _ + g _ = f v + g v; rw [hf.1.1, hg.1.1]
      · intro a v; change f _ + g _ = f v + g v; rw [hf.1.2, hg.1.2]
    · constructor
      · intro a v; change f _ + g _ = f v + g v; rw [hf.2.1, hg.2.1]
      · intro p hp v
        change f _ + g _ = Equiv.Perm.sign p • (f v + g v)
        rw [hf.2.2 p hp, hg.2.2 p hp, smul_add]
  smul_mem' := by
    intro z f hf
    constructor
    · constructor
      · intro a v; change z • f _ = z • f v; rw [hf.1.1]
      · intro a v; change z • f _ = z • f v; rw [hf.1.2]
    · constructor
      · intro a v; change z • f _ = z • f v; rw [hf.2.1]
      · intro p hp v
        change z • f _ = _
        rw [hf.2.2 p hp, smul_comm]
        rfl

abbrev Coefficients := ↥(coefficientSubmodule s)

/-- The residual Hom with the four explicit simultaneous exchange equations. -/
abbrev statisticsSubmodule : Submodule ℂ (Hom s) where
  carrier := {k | SatisfiesFlavorStatistics (fun t => homCoordinates s k t)}
  zero_mem' := by
    intro g t
    ext p q
    simp [homCoordinates, MultilinearInvariantHom.toMultilinear,
      SixQuarkSpeciesQuotient.transform]
  add_mem' := by
    intro k l hk hl g t
    ext p q
    have h := congrArg₂ (· + ·) (congrFun (congrFun (hk g t) p) q)
      (congrFun (congrFun (hl g t) p) q)
    simp [homCoordinates, MultilinearInvariantHom.toMultilinear,
      SixQuarkSpeciesQuotient.transform, mul_add, Finset.sum_add_distrib] at h ⊢
    linear_combination h
  smul_mem' := by
    intro z k hk g t
    ext p q
    have h := congrArg (z * ·) (congrFun (congrFun (hk g t) p) q)
    simpa [homCoordinates, MultilinearInvariantHom.toMultilinear,
      SixQuarkSpeciesQuotient.transform, smul_eq_mul, Finset.mul_sum,
      mul_left_comm, mul_assoc] using h

abbrev StatisticsHom := ↥(statisticsSubmodule s)

def toStatisticsHom (f : Coefficients s) : StatisticsHom s := by
  refine ⟨residualHom s f.val f.property.1 f.property.2.1, ?_⟩
  have hc : (fun t => homCoordinates s
      (residualHom s f.val f.property.1 f.property.2.1) t) = flavorCoordinates f.val := by
    funext t
    rw [homCoordinates_residualHom, flavorCoordinatesMap_apply]
  change SatisfiesFlavorStatistics (fun t => homCoordinates s
    (residualHom s f.val f.property.1 f.property.2.1) t)
  rw [hc]
  exact (statistics_iff f.val f.property.1).mp
    ((swaps_iff_species f.val).mpr f.property.2.2)

def fromStatisticsHom (k : StatisticsHom s) : Coefficients s := by
  refine ⟨assembleHom s k.val, assembleHom_invariant s k.val,
    assembleHom_residualInvariant s k.val, ?_⟩
  apply (swaps_iff_species _).mp
  apply (statistics_iff _ (assembleHom_invariant s k.val)).mpr
  change SatisfiesFlavorStatistics (flavorCoordinates (assemble (homCoordinates s k.val)))
  rw [coordinates_assemble]
  exact k.property

/-- Complete constrained residual Hom classification on common-carrier slots.
The equations still permute flavor inputs; no dimension-two premise occurs. -/
def statisticsEquiv : Coefficients s ≃ StatisticsHom s where
  toFun := toStatisticsHom s
  invFun := fromStatisticsHom s
  left_inv f := by
    apply Subtype.ext
    exact assembleHom_residualHom s f.val f.property.1 f.property.2.1
  right_inv k := by
    apply Subtype.ext
    exact residualHom_assembleHom s k.val

/-- Linear, rather than merely set-theoretic, constrained classification. -/
def statisticsLinearEquiv : Coefficients s ≃ₗ[ℂ] StatisticsHom s :=
  { statisticsEquiv s with
    map_add' := by
      intro f g
      apply Subtype.ext
      apply IntertwiningMap.ext
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro t
      change PiTensorProduct.lift (flavorCoordinatesMap (f + g).val)
        (PiTensorProduct.tprod ℂ t) =
          PiTensorProduct.lift (flavorCoordinatesMap f.val) (PiTensorProduct.tprod ℂ t) +
            PiTensorProduct.lift (flavorCoordinatesMap g.val) (PiTensorProduct.tprod ℂ t)
      simp only [PiTensorProduct.lift.tprod, flavorCoordinatesMap_apply]
      change coordinateLinear (fixedFlavor (f.val + g.val) t) =
        coordinateLinear (fixedFlavor f.val t) + coordinateLinear (fixedFlavor g.val t)
      have he : fixedFlavor (f.val + g.val) t = fixedFlavor f.val t + fixedFlavor g.val t := by
        ext q; rfl
      rw [he, map_add]
    map_smul' := by
      intro z f
      apply Subtype.ext
      apply IntertwiningMap.ext
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

theorem exists_nonzero_statistics_iff :
    (∃ f : Coefficients s, f ≠ 0) ↔ ∃ k : StatisticsHom s, k ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨statisticsLinearEquiv s f, fun h => hf ((statisticsLinearEquiv s).map_eq_zero_iff.mp h)⟩
  · rintro ⟨k, hk⟩
    exact ⟨(statisticsLinearEquiv s).symm k,
      fun h => hk ((statisticsLinearEquiv s).symm.map_eq_zero_iff.mp h)⟩
end Statistics

end
end Physics.SixQuarkFlavorResidualHom
