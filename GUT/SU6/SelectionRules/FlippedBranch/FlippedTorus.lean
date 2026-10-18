import GUT.SU6.Characters.ActualRestriction
import GUT.SU6.Characters.LaurentEvaluation

/-!
# The flipped diagonal subtorus inside SU(6)

The Laurent model used in the flipped obstruction is not the whole maximal
torus of SU(6).  It is the subtorus cut out by `z4 * z5 = 1`, together with the
SU(6) determinant relation.  On this subtorus the sixth coordinate is forced to
be `(z1*z2*z3)^-1`, matching `Flipped.AlgebraicTorusPoint.z6`.
-/

namespace GUT
namespace FlippedTorus

noncomputable section

abbrev SU6 := ActualRestriction.SU6
abbrev DiagonalSU6Point := ActualRestriction.DiagonalSU6Point

structure FlippedDiagonalSU6Point where
  toDiagonal : DiagonalSU6Point
  weak_relation : toDiagonal.coords 3 * toDiagonal.coords 4 = 1

namespace FlippedDiagonalSU6Point

def coords (t : FlippedDiagonalSU6Point) : WeylMatrix.I6 -> ℂ :=
  t.toDiagonal.coords

theorem det_product (t : FlippedDiagonalSU6Point) :
    ∏ i, t.coords i = 1 := by
  have hdet : (Matrix.diagonal t.toDiagonal.coords).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp t.toDiagonal.mem).2
  simpa [coords, Matrix.det_diagonal] using hdet

theorem coord_ne_zero (t : FlippedDiagonalSU6Point) (i : WeylMatrix.I6) :
    t.coords i ≠ 0 := by
  have hprodNe : (∏ j, t.coords j) ≠ 0 := by
    rw [t.det_product]
    norm_num
  rw [Finset.prod_ne_zero_iff] at hprodNe
  exact hprodNe i (Finset.mem_univ i)

def coordUnit (t : FlippedDiagonalSU6Point) (i : WeylMatrix.I6) : ℂˣ :=
  Units.mk0 (t.coords i) (t.coord_ne_zero i)

def swap36 (t : FlippedDiagonalSU6Point) : FlippedDiagonalSU6Point where
  toDiagonal := ActualRestriction.DiagonalSU6Point.swap36 t.toDiagonal
  weak_relation := by
    change
      t.toDiagonal.coords (WeylMatrix.swap36 3) *
        t.toDiagonal.coords (WeylMatrix.swap36 4) = 1
    have h3 : WeylMatrix.swap36 3 = 3 := by decide
    have h4 : WeylMatrix.swap36 4 = 4 := by decide
    simpa [h3, h4] using t.weak_relation

def toAlgebraicTorusPoint
    (t : FlippedDiagonalSU6Point) : Flipped.AlgebraicTorusPoint where
  z1 := t.coordUnit 0
  z2 := t.coordUnit 1
  z3 := t.coordUnit 2
  z4 := t.coordUnit 3

theorem coord5_eq_inv_colorProduct (t : FlippedDiagonalSU6Point) :
    t.coords 5 = (t.coords 0 * t.coords 1 * t.coords 2)⁻¹ := by
  have hdet := t.det_product
  rw [Fin.prod_univ_six] at hdet
  have hmain : t.coords 0 * t.coords 1 * t.coords 2 * t.coords 5 = 1 := by
    have hweak : t.coords 3 * t.coords 4 = 1 := by
      simpa [coords] using t.weak_relation
    calc
      t.coords 0 * t.coords 1 * t.coords 2 * t.coords 5
          = (t.coords 0 * t.coords 1 * t.coords 2 * t.coords 5) *
              (t.coords 3 * t.coords 4) := by
                rw [hweak]
                ring
      _ = t.coords 0 * t.coords 1 * t.coords 2 *
            t.coords 3 * t.coords 4 * t.coords 5 := by
                ring
      _ = 1 := hdet
  exact eq_inv_of_mul_eq_one_right hmain

theorem coordUnit5_eq_z6 (t : FlippedDiagonalSU6Point) :
    t.coordUnit 5 = (t.toAlgebraicTorusPoint).z6 := by
  apply Units.ext
  simp [coordUnit, toAlgebraicTorusPoint, Flipped.AlgebraicTorusPoint.z6,
    coord5_eq_inv_colorProduct]

theorem toAlgebraicTorusPoint_swap36 (t : FlippedDiagonalSU6Point) :
    toAlgebraicTorusPoint (swap36 t) =
      Flipped.AlgebraicTorusPoint.swap36 (toAlgebraicTorusPoint t) := by
  apply Flipped.AlgebraicTorusPoint.ext
  · apply Units.ext
    have h : WeylMatrix.swap36 0 = 0 := by decide
    simp [toAlgebraicTorusPoint, coordUnit, coords, swap36,
      ActualRestriction.DiagonalSU6Point.swap36,
      Flipped.AlgebraicTorusPoint.swap36, h]
  · apply Units.ext
    have h : WeylMatrix.swap36 1 = 1 := by decide
    simp [toAlgebraicTorusPoint, coordUnit, coords, swap36,
      ActualRestriction.DiagonalSU6Point.swap36,
      Flipped.AlgebraicTorusPoint.swap36, h]
  · simpa [toAlgebraicTorusPoint, coordUnit, coords, swap36,
      ActualRestriction.DiagonalSU6Point.swap36,
      Flipped.AlgebraicTorusPoint.swap36,
      (by decide : WeylMatrix.swap36 2 = 5)]
      using t.coordUnit5_eq_z6
  · apply Units.ext
    have h : WeylMatrix.swap36 3 = 3 := by decide
    simp [toAlgebraicTorusPoint, coordUnit, coords, swap36,
      ActualRestriction.DiagonalSU6Point.swap36,
      Flipped.AlgebraicTorusPoint.swap36, h]

def restrictedCharacter
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) (t : FlippedDiagonalSU6Point) : ℂ :=
  ActualRestriction.restrictedCharacter ρ t.toDiagonal

theorem restrictedCharacter_swap36_fixed
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ SU6 V) (t : FlippedDiagonalSU6Point) :
    restrictedCharacter ρ (swap36 t) = restrictedCharacter ρ t := by
  exact ActualRestriction.restrictedCharacter_swap36_fixed ρ t.toDiagonal

end FlippedDiagonalSU6Point

end

end FlippedTorus
end GUT
