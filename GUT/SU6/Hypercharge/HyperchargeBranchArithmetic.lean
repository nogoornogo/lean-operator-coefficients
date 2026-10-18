import GUT.SU6.Hypercharge.ActualCompactCentralizerLattice
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Tactic

/-!
# Arithmetic core of the standard/flipped hypercharge branches

The physical centralizer cocharacter lattice has color and weak exponents
`(m,n)` and determinant-forced singlet exponent `-(3*m+2*n)`.  This file
isolates the elementary but exact part of the proposed standard/flipped
classification.

For a primitive cocharacter:

* a neutral weak block gives `(m,n) = (1,0)` up to sign;
* a neutral singlet block gives `(m,n) = (-2,3)` up to sign;
* a neutral color block gives the additional arithmetic possibility
  `(m,n) = (0,1)` up to sign.

Consequently, after excluding a neutral color block and fixing the physical
orientation, weak-or-singlet neutrality gives exactly the flipped or standard
pair.  Deriving that neutrality disjunction from the full SM-only
representation-ring hypothesis is deliberately not asserted here.
-/

namespace GUT
namespace HyperchargeBranchArithmetic

open ActualCompactCentralizer
open WeakDoubletEmbeddingClassification
open ActualBlockCentralizer
open CompactEmbeddingClassification

/-- The determinant-forced exponent on the one-dimensional block. -/
def singletExponent (mn : ℤ × ℤ) : ℤ :=
  -(3 * mn.1 + 2 * mn.2)

/-- The standard `6Y = (-2,-2,-2,3,3,0)` cocharacter. -/
def standardPair : ℤ × ℤ := (-2, 3)

/-- The flipped `6Y = (1,1,1,0,0,-3)` cocharacter. -/
def flippedPair : ℤ × ℤ := (1, 0)

/-- The third arithmetic neutral-block possibility, which has neutral color. -/
def colorNeutralPair : ℤ × ℤ := (0, 1)

/-- An orientation convention for the three ways a defining block can be
neutral.  The positive exponent is chosen on the nontrivial weak or color
block. -/
def HasOrientedNeutralBlock (mn : ℤ × ℤ) : Prop :=
  (mn.1 = 0 ∧ 0 < mn.2) ∨
    (mn.2 = 0 ∧ 0 < mn.1) ∨
    (singletExponent mn = 0 ∧ 0 < mn.2)

@[simp]
theorem singletExponent_standard : singletExponent standardPair = 0 := by
  norm_num [singletExponent, standardPair]

@[simp]
theorem singletExponent_flipped : singletExponent flippedPair = -3 := by
  norm_num [singletExponent, flippedPair]

@[simp]
theorem standardPair_primitive : standardPair.1.gcd standardPair.2 = 1 := by
  norm_num [standardPair]

@[simp]
theorem flippedPair_primitive : flippedPair.1.gcd flippedPair.2 = 1 := by
  norm_num [flippedPair]

@[simp]
theorem colorNeutralPair_primitive :
    colorNeutralPair.1.gcd colorNeutralPair.2 = 1 := by
  norm_num [colorNeutralPair]

/-- Primitive neutral-block arithmetic alone does not imply the proposed
two-branch conclusion: the color-neutral pair is a third possibility. -/
theorem colorNeutralPair_not_flipped_or_standard :
    colorNeutralPair ≠ flippedPair ∧ colorNeutralPair ≠ standardPair := by
  norm_num [colorNeutralPair, flippedPair, standardPair]

private theorem eq_one_or_neg_one_of_gcd_right_zero
    {m : ℤ} (h : m.gcd 0 = 1) : m = 1 ∨ m = -1 := by
  apply Int.isUnit_iff.mp
  apply Int.isUnit_iff_natAbs_eq.mpr
  simpa [Int.gcd_def] using h

private theorem eq_one_or_neg_one_of_gcd_left_zero
    {n : ℤ} (h : (0 : ℤ).gcd n = 1) : n = 1 ∨ n = -1 := by
  apply Int.isUnit_iff.mp
  apply Int.isUnit_iff_natAbs_eq.mpr
  simpa [Int.gcd_def] using h

/-- A primitive cocharacter with neutral weak block is the flipped pair up to
reversal of the circle parameter. -/
theorem eq_flipped_or_neg_of_primitive_of_weak_zero
    (mn : ℤ × ℤ) (hPrimitive : mn.1.gcd mn.2 = 1)
    (hWeak : mn.2 = 0) :
    mn = flippedPair ∨ mn = (-1, 0) := by
  rcases mn with ⟨m, n⟩
  simp only at hPrimitive hWeak
  subst n
  rcases eq_one_or_neg_one_of_gcd_right_zero hPrimitive with hm | hm
  · left
    ext <;> simp [flippedPair, hm]
  · right
    ext <;> simp [hm]

/-- A primitive cocharacter with neutral color block is the color-neutral pair
up to reversal of the circle parameter. -/
theorem eq_colorNeutral_or_neg_of_primitive_of_color_zero
    (mn : ℤ × ℤ) (hPrimitive : mn.1.gcd mn.2 = 1)
    (hColor : mn.1 = 0) :
    mn = colorNeutralPair ∨ mn = (0, -1) := by
  rcases mn with ⟨m, n⟩
  simp only at hPrimitive hColor
  subst m
  rcases eq_one_or_neg_one_of_gcd_left_zero hPrimitive with hn | hn
  · left
    ext <;> simp [colorNeutralPair, hn]
  · right
    ext <;> simp [hn]

/-- A primitive cocharacter with neutral singlet block is the standard pair up
to reversal of the circle parameter. -/
theorem eq_standard_or_neg_of_primitive_of_singlet_zero
    (mn : ℤ × ℤ) (hPrimitive : mn.1.gcd mn.2 = 1)
    (hSinglet : singletExponent mn = 0) :
    mn = standardPair ∨ mn = (2, -3) := by
  rcases mn with ⟨m, n⟩
  change m.gcd n = 1 at hPrimitive
  change -(3 * m + 2 * n) = 0 at hSinglet
  have hTwoDvdThreeM : (2 : ℤ) ∣ 3 * m := by
    use -n
    omega
  have hTwoDvdM : (2 : ℤ) ∣ m := by
    rcases Int.prime_two.dvd_or_dvd hTwoDvdThreeM with hTwoDvdThree | hTwoDvdM
    · norm_num at hTwoDvdThree
    · exact hTwoDvdM
  obtain ⟨k, hk⟩ := hTwoDvdM
  have hn : n = -3 * k := by omega
  have hkDvdM : k ∣ m := by
    use 2
    omega
  have hkDvdN : k ∣ n := by
    use -3
    omega
  have hkDvdOne : k ∣ (1 : ℤ) := by
    have hkDvdGcd : k ∣ (m.gcd n : ℤ) :=
      Int.dvd_coe_gcd hkDvdM hkDvdN
    simpa [hPrimitive] using hkDvdGcd
  have hkUnit : IsUnit k := isUnit_iff_dvd_one.mpr hkDvdOne
  rcases Int.isUnit_iff.mp hkUnit with hkOne | hkNeg
  · right
    apply Prod.ext <;> simp_all
  · left
    apply Prod.ext <;> simp_all [standardPair]

/-- All primitive cocharacters with at least one neutral defining block.  The
color-neutral pair is displayed explicitly rather than silently discarded. -/
theorem primitive_neutral_block_classification
    (mn : ℤ × ℤ) (hPrimitive : mn.1.gcd mn.2 = 1)
    (hNeutral : mn.1 = 0 ∨ mn.2 = 0 ∨ singletExponent mn = 0) :
    mn = colorNeutralPair ∨ mn = (0, -1) ∨
      mn = flippedPair ∨ mn = (-1, 0) ∨
      mn = standardPair ∨ mn = (2, -3) := by
  rcases hNeutral with hColor | hWeak | hSinglet
  · rcases eq_colorNeutral_or_neg_of_primitive_of_color_zero
      mn hPrimitive hColor with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases eq_flipped_or_neg_of_primitive_of_weak_zero
      mn hPrimitive hWeak with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · rcases eq_standard_or_neg_of_primitive_of_singlet_zero
      mn hPrimitive hSinglet with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

/-- With the physical orientation fixed, primitive weak-or-singlet neutrality
gives exactly the flipped or standard hypercharge pair. -/
theorem eq_flipped_or_standard_of_primitive_of_oriented_neutrality
    (mn : ℤ × ℤ) (hPrimitive : mn.1.gcd mn.2 = 1)
    (hNeutral :
      (mn.2 = 0 ∧ 0 < mn.1) ∨
        (singletExponent mn = 0 ∧ 0 < mn.2)) :
    mn = flippedPair ∨ mn = standardPair := by
  rcases hNeutral with ⟨hWeak, hColorPos⟩ | ⟨hSinglet, hWeakPos⟩
  · rcases eq_flipped_or_neg_of_primitive_of_weak_zero
      mn hPrimitive hWeak with h | h
    · exact Or.inl h
    · subst mn
      norm_num at hColorPos
  · rcases eq_standard_or_neg_of_primitive_of_singlet_zero
      mn hPrimitive hSinglet with h | h
    · exact Or.inr h
    · subst mn
      norm_num at hWeakPos

/-- Once the separately obstructed color-neutral pair is removed, the
oriented primitive neutral-block classification has exactly the flipped and
standard branches. -/
theorem eq_flipped_or_standard_of_primitive_of_oriented_neutralBlock_of_ne_color
    (mn : ℤ × ℤ) (hPrimitive : mn.1.gcd mn.2 = 1)
    (hNeutral : HasOrientedNeutralBlock mn)
    (hNotColor : mn ≠ colorNeutralPair) :
    mn = flippedPair ∨ mn = standardPair := by
  rcases hNeutral with hColor | hWeak | hSinglet
  · have hColorZero := hColor.1
    have hColorPositive := hColor.2
    rcases eq_colorNeutral_or_neg_of_primitive_of_color_zero
      mn hPrimitive hColorZero with h | h
    · exact False.elim (hNotColor h)
    · subst mn
      norm_num at hColorPositive
  · exact eq_flipped_or_standard_of_primitive_of_oriented_neutrality
      mn hPrimitive (Or.inl hWeak)
  · exact eq_flipped_or_standard_of_primitive_of_oriented_neutrality
      mn hPrimitive (Or.inr hSinglet)

/-- For an actual physical-centralizer circle, injectivity supplies the
primitive hypothesis.  Thus the remaining input needed for the two-branch
conclusion is precisely the stated oriented-neutrality condition. -/
theorem physicalCircleHom_eq_flipped_or_standard_of_injective_of_oriented_neutrality
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ)
    (hInjective : Function.Injective (physicalCircleHom iota W mn))
    (hNeutral :
      (mn.2 = 0 ∧ 0 < mn.1) ∨
        (singletExponent mn = 0 ∧ 0 < mn.2)) :
    mn = flippedPair ∨ mn = standardPair := by
  apply eq_flipped_or_standard_of_primitive_of_oriented_neutrality mn
  · exact (physicalCircleHom_injective_iff iota W mn).mp hInjective
  · exact hNeutral

/-- Actual-circle form of the complete oriented neutral-block reduction after
the color-neutral pair has been excluded by a separate character argument. -/
theorem physicalCircleHom_eq_flipped_or_standard_of_injective_of_neutralBlock_of_ne_color
    (iota : ProductGroup →* SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (mn : ℤ × ℤ)
    (hInjective : Function.Injective (physicalCircleHom iota W mn))
    (hNeutral : HasOrientedNeutralBlock mn)
    (hNotColor : mn ≠ colorNeutralPair) :
    mn = flippedPair ∨ mn = standardPair := by
  apply
    eq_flipped_or_standard_of_primitive_of_oriented_neutralBlock_of_ne_color
      mn
  · exact (physicalCircleHom_injective_iff iota W mn).mp hInjective
  · exact hNeutral
  · exact hNotColor

end HyperchargeBranchArithmetic
end GUT
