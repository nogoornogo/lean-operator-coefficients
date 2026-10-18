import GUT.SU6.Hypercharge.ActualCompactCentralizerTopology
import Math.LieGroups.Torus.CircleHomLattice

open Math

/-!
# The circle-homomorphism lattice of the actual compact centralizer

The checked continuous equivalence between the physical centralizer and the
two-torus transports the integer exponent classification of continuous circle
homomorphisms to the actual `SU(6)` matrices.  In block coordinates, an
integer pair `(m, n)` acts with exponents

`(m, n, -(3 * m + 2 * n))`

on the color, weak, and singlet constituents respectively.
-/

namespace GUT
namespace ActualCompactCentralizer

open WeakDoubletEmbeddingClassification
open CompactEmbeddingClassification
open CircleHomLattice
open ActualBlockCentralizer

noncomputable section

/-- The physical centralizer circle with color and weak exponent pair
`(m, n)`. -/
def physicalCircleHom
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) : Circle →ₜ* PhysicalCentralizer iota :=
  ((physicalCentralizerContinuousMulEquivTorus iota W).symm :
      (Circle × Circle) →ₜ* PhysicalCentralizer iota).comp
    (circlePairPowerHom mn)

@[simp]
theorem physicalCircleHom_toTorus
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (z : Circle) :
    physicalCentralizerContinuousMulEquivTorus iota W
        (physicalCircleHom iota W mn z) =
      (z ^ mn.1, z ^ mn.2) := by
  exact (physicalCentralizerContinuousMulEquivTorus iota W).apply_symm_apply _

/-- Every continuous circle homomorphism into the actual physical
centralizer has a unique integer exponent pair. -/
theorem existsUnique_eq_physicalCircleHom
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (f : Circle →ₜ* PhysicalCentralizer iota) :
    ∃! mn : ℤ × ℤ, f = physicalCircleHom iota W mn := by
  let fTorus : Circle →ₜ* Circle × Circle :=
    (physicalCentralizerContinuousMulEquivTorus iota W :
      PhysicalCentralizer iota →ₜ* Circle × Circle).comp f
  obtain ⟨mn, hmn, hmn_unique⟩ :=
    CircleHomLattice.existsUnique_eq_circlePairPowerHom fTorus
  refine ⟨mn, ?_, ?_⟩
  · apply ContinuousMonoidHom.ext
    intro z
    have hAtZ := congrArg
      (fun g : Circle →ₜ* Circle × Circle => g z) hmn
    have hBack := congrArg
      (physicalCentralizerContinuousMulEquivTorus iota W).symm hAtZ
    simpa [fTorus, physicalCircleHom] using hBack
  · intro pq hpq
    apply hmn_unique pq
    apply ContinuousMonoidHom.ext
    intro z
    have hAtZ := congrArg
      (fun g : Circle →ₜ* PhysicalCentralizer iota => g z) hpq
    change physicalCentralizerContinuousMulEquivTorus iota W (f z) =
      (z ^ pq.1, z ^ pq.2)
    rw [hAtZ]
    exact physicalCircleHom_toTorus iota W pq z

/-- The cocharacter lattice of the actual physical centralizer, as an
explicit equivalence of underlying types. -/
def integerPairEquivPhysicalCircleHom
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota)) :
    (ℤ × ℤ) ≃ (Circle →ₜ* PhysicalCentralizer iota) :=
  Equiv.ofBijective (physicalCircleHom iota W)
    ⟨fun mn pq h => ((existsUnique_eq_physicalCircleHom iota W
        (physicalCircleHom iota W mn)).unique
          (y₁ := pq) (y₂ := mn) h rfl).symm,
      fun f => by
        obtain ⟨mn, hmn⟩ :=
          (existsUnique_eq_physicalCircleHom iota W f).exists
        exact ⟨mn, hmn.symm⟩⟩

/-- A physical centralizer circle is an embedding exactly when its integer
cocharacter is primitive. -/
theorem physicalCircleHom_injective_iff
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) :
    Function.Injective (physicalCircleHom iota W mn) ↔
      mn.1.gcd mn.2 = 1 := by
  rw [← CircleHomLattice.circlePairPowerHom_injective_iff]
  constructor
  · intro hPhysical z w hTorus
    apply hPhysical
    change (physicalCentralizerContinuousMulEquivTorus iota W).symm
        (circlePairPowerHom mn z) =
      (physicalCentralizerContinuousMulEquivTorus iota W).symm
        (circlePairPowerHom mn w)
    rw [hTorus]
  · intro hTorus z w hPhysical
    apply hTorus
    have hMapped := congrArg
      (physicalCentralizerContinuousMulEquivTorus iota W) hPhysical
    simpa only [physicalCircleHom_toTorus,
      CircleHomLattice.circlePairPowerHom_apply] using hMapped

/-- In explicit coefficient coordinates, the physical circle is reconstructed
from its two independent integer powers. -/
theorem physicalCircleHom_apply
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (z : Circle) :
    physicalCircleHom iota W mn z =
      reconstructedCentralizerElement iota W
        (CompactBlockCentralizer.ofColorWeak
          (z ^ mn.1, z ^ mn.2)) :=
  rfl

theorem physicalCircleHom_compactBlockCoefficients
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (z : Circle) :
    compactBlockCoefficients iota W (physicalCircleHom iota W mn z) =
      CompactBlockCentralizer.ofColorWeak
        (z ^ mn.1, z ^ mn.2) := by
  rw [physicalCircleHom_apply,
    compactBlockCoefficients_reconstructed]

@[simp]
theorem physicalCircleHom_colorExponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (z : Circle) :
    ((compactBlockCoefficients iota W
      (physicalCircleHom iota W mn z) :
        CompactBlockCentralizer.BlockCoefficients).1) = z ^ mn.1 := by
  rw [physicalCircleHom_compactBlockCoefficients]
  rfl

@[simp]
theorem physicalCircleHom_weakExponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (z : Circle) :
    ((compactBlockCoefficients iota W
      (physicalCircleHom iota W mn z) :
        CompactBlockCentralizer.BlockCoefficients).2.1) = z ^ mn.2 := by
  rw [physicalCircleHom_compactBlockCoefficients]
  rfl

@[simp]
theorem physicalCircleHom_singletExponent
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ) (z : Circle) :
    ((compactBlockCoefficients iota W
      (physicalCircleHom iota W mn z) :
        CompactBlockCentralizer.BlockCoefficients).2.2) =
      z ^ (-(3 * mn.1 + 2 * mn.2)) := by
  rw [physicalCircleHom_compactBlockCoefficients]
  change ((z ^ mn.1) ^ 3 * (z ^ mn.2) ^ 2)⁻¹ =
    z ^ (-(3 * mn.1 + 2 * mn.2))
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    ← zpow_add, ← zpow_neg]
  congr 1
  omega

/-!
## Coordinates in the checked anti-Hermitian real form
-/

/-- The real `Y5/X` coefficients associated to an integer exponent pair. -/
def integerPairToRealExtra (mn : ℤ × ℤ) : ℝ × ℝ :=
  (((mn.2 : ℝ) - (mn.1 : ℝ)) / 5,
    (3 * (mn.1 : ℝ) + 2 * (mn.2 : ℝ)) / 5)

/-- The `Y5/X` color coefficient recovers the first integer exponent. -/
theorem integerPairToRealExtra_color (mn : ℤ × ℤ) :
    -2 * (integerPairToRealExtra mn).1 +
        (integerPairToRealExtra mn).2 = (mn.1 : ℝ) := by
  simp [integerPairToRealExtra]
  ring

/-- The `Y5/X` weak coefficient recovers the second integer exponent. -/
theorem integerPairToRealExtra_weak (mn : ℤ × ℤ) :
    3 * (integerPairToRealExtra mn).1 +
        (integerPairToRealExtra mn).2 = (mn.2 : ℝ) := by
  simp [integerPairToRealExtra]
  ring

/-- The `Y5/X` singlet coefficient is the determinant-forced exponent. -/
theorem integerPairToRealExtra_singlet (mn : ℤ × ℤ) :
    -5 * (integerPairToRealExtra mn).2 =
      -(3 * (mn.1 : ℝ) + 2 * (mn.2 : ℝ)) := by
  simp [integerPairToRealExtra]
  ring

/-- Distinct integer cocharacters have distinct `Y5/X` real coordinates. -/
theorem integerPairToRealExtra_injective :
    Function.Injective integerPairToRealExtra := by
  intro mn pq h
  apply Prod.ext
  · have hColor := congrArg
      (fun p : ℝ × ℝ => -2 * p.1 + p.2) h
    rw [integerPairToRealExtra_color,
      integerPairToRealExtra_color] at hColor
    exact_mod_cast hColor
  · have hWeak := congrArg
      (fun p : ℝ × ℝ => 3 * p.1 + p.2) h
    rw [integerPairToRealExtra_weak,
      integerPairToRealExtra_weak] at hWeak
    exact_mod_cast hWeak

end


end ActualCompactCentralizer
end GUT
