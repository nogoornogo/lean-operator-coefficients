import GUT.SU6.Characters.NormalizedLaurent

/-!
# Explicit torus eigenbasis certificates for basic SU(6) representations

This file starts the constructive side of the `SU6TorusEigenbasisTheory`
interface.  Mathlib has general Lie-theoretic weight-space infrastructure, but
not a ready-made theorem turning every continuous/smooth/algebraic finite
dimensional `SU(6)` representation into the project-specific
`TorusEigenbasis` certificate.  We therefore build the certificates directly
for the representation-building blocks.

The first block is the defining six-dimensional representation.  Its
restriction to the flipped diagonal torus is diagonal in the standard basis,
with weights

* `z₁, z₂, z₃, z₄`,
* `z₅ = z₄⁻¹`,
* `z₆ = (z₁ z₂ z₃)⁻¹`.

This is the concrete bridge from the actual matrix representation to the
Laurent monomial model.
-/

namespace GUT

namespace FlippedTorus
namespace FlippedDiagonalSU6Point

noncomputable section

theorem coord4_eq_inv_coord3 (t : FlippedDiagonalSU6Point) :
    t.coords 4 = (t.coords 3)⁻¹ := by
  have hweak : t.coords 3 * t.coords 4 = 1 := by
    simpa [coords] using t.weak_relation
  exact eq_inv_of_mul_eq_one_right hweak

theorem coordUnit4_eq_z5 (t : FlippedDiagonalSU6Point) :
    t.coordUnit 4 = (t.toAlgebraicTorusPoint).z5 := by
  apply Units.ext
  simp [coordUnit, toAlgebraicTorusPoint, Flipped.AlgebraicTorusPoint.z5,
    coord4_eq_inv_coord3]

end

end FlippedDiagonalSU6Point
end FlippedTorus

namespace FundamentalRepresentation

open VirtualRestriction WeightTheory

noncomputable section

abbrev SU6 := ActualRestriction.SU6
abbrev I6 := WeylMatrix.I6
abbrev Std := I6 -> ℂ

/-- The defining action of `SU(6)` on `ℂ⁶`. -/
def rho : Representation ℂ SU6 Std where
  toFun g := Matrix.toLin' ((g : SU6) : Matrix I6 I6 ℂ)
  map_one' := by
    change Matrix.toLin' (1 : Matrix I6 I6 ℂ) = LinearMap.id
    exact Matrix.toLin'_one
  map_mul' := by
    intro g h
    change
      Matrix.toLin'
          (((g : SU6) : Matrix I6 I6 ℂ) *
            ((h : SU6) : Matrix I6 I6 ℂ)) =
        (Matrix.toLin' ((g : SU6) : Matrix I6 I6 ℂ)).comp
          (Matrix.toLin' ((h : SU6) : Matrix I6 I6 ℂ))
    exact Matrix.toLin'_mul ((g : SU6) : Matrix I6 I6 ℂ)
      ((h : SU6) : Matrix I6 I6 ℂ)

/-- The defining six-dimensional actual representation. -/
def actual : VirtualRestriction.ActualSU6Representation where
  V := Std
  rho := rho

/-- The six torus weights of the defining representation in flipped coordinates. -/
def weight : I6 -> Flipped.Exp :=
  ![
    { z1 := 1, z2 := 0, z3 := 0, z4 := 0 },
    { z1 := 0, z2 := 1, z3 := 0, z4 := 0 },
    { z1 := 0, z2 := 0, z3 := 1, z4 := 0 },
    { z1 := 0, z2 := 0, z3 := 0, z4 := 1 },
    { z1 := 0, z2 := 0, z3 := 0, z4 := -1 },
    { z1 := -1, z2 := -1, z3 := -1, z4 := 0 }
  ]

theorem weight_eval_eq_coord
    (t : FlippedTorus.FlippedDiagonalSU6Point) (i : I6) :
    Flipped.Exp.eval (weight i) t.toAlgebraicTorusPoint =
      (t.coordUnit i : ℂ) := by
  fin_cases i <;>
    simp [weight, Flipped.Exp.eval, Flipped.Exp.evalUnit,
      FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint,
      Flipped.AlgebraicTorusPoint.z5, Flipped.AlgebraicTorusPoint.z6,
      FlippedTorus.FlippedDiagonalSU6Point.coordUnit4_eq_z5,
      FlippedTorus.FlippedDiagonalSU6Point.coordUnit5_eq_z6]
  ring

theorem rho_diagonal_basis
    (t : FlippedTorus.FlippedDiagonalSU6Point) (i : I6) :
    rho t.toDiagonal.toSU6 (Pi.basisFun ℂ I6 i) =
      (t.coordUnit i : ℂ) • Pi.basisFun ℂ I6 i := by
  change
    Matrix.toLin' (Matrix.diagonal t.toDiagonal.coords)
        (Pi.basisFun ℂ I6 i) =
      (t.coordUnit i : ℂ) • Pi.basisFun ℂ I6 i
  ext j
  by_cases hji : j = i
  · subst j
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.basisFun_apply,
      FlippedTorus.FlippedDiagonalSU6Point.coordUnit,
      FlippedTorus.FlippedDiagonalSU6Point.coords]
  · simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.basisFun_apply,
      FlippedTorus.FlippedDiagonalSU6Point.coordUnit,
      FlippedTorus.FlippedDiagonalSU6Point.coords, hji]

/--
The standard basis is a torus eigenbasis for the defining representation,
with the six flipped Laurent weights listed in `weight`.
-/
def torusEigenbasis : TorusEigenbasis actual where
  ι := I6
  basis := Pi.basisFun ℂ I6
  weight := weight
  action_on_basis := by
    intro t i
    change
      rho t.toDiagonal.toSU6 (Pi.basisFun ℂ I6 i) =
        Flipped.Exp.eval (weight i) t.toAlgebraicTorusPoint •
          Pi.basisFun ℂ I6 i
    rw [rho_diagonal_basis t i, weight_eval_eq_coord t i]

/--
The defining representation is one concrete `PhysicallyAdmissibleSU6Representation`:
its restricted character is represented by a normalized Laurent polynomial
through the common faithful evaluator.
-/
def physicallyAdmissible : PhysicallyAdmissibleSU6Representation where
  toActual := actual
  eigenbasis := torusEigenbasis

theorem normalizedCharacter_evaluates
    (t : FlippedTorus.FlippedDiagonalSU6Point) :
    NormalizedVirtualRestriction.diagonalLaurentEval
        (physicallyAdmissible.normalizedCharacter).poly t =
      actual.restrictedCharacter t := by
  exact
    (physicallyAdmissible.normalizedCharacter).evaluates_restrictedCharacter t

end

end FundamentalRepresentation
end GUT
