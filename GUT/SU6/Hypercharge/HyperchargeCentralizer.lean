import Mathlib.Tactic

/-!
# The rank-two block-scalar hypercharge space

For the standard semisimple block decomposition

`6 = (3,1) + (1,2) + (1,1)`,

an infinitesimal centralizer element is scalar on the three blocks.  Once that
block-scalar statement is supplied, membership in `su(6)` is exactly the trace
condition `3*c + 2*w + s = 0`.  This module proves that the resulting space is
spanned uniquely by the standard `SU(5)`-like generator and one extra
centralizer generator.

The separate Schur-theoretic statement that every centralizer element is
block-scalar is not asserted here.
-/

namespace GUT
namespace HyperchargeCentralizer

/-- Coefficients of a block-scalar traceless diagonal generator on blocks of
dimensions `3`, `2`, and `1`. -/
@[ext]
structure Generator where
  color : ℚ
  weak : ℚ
  singlet : ℚ
  traceless : 3 * color + 2 * weak + singlet = 0

/-- `6Y = (-2,-2,-2,3,3,0)` in block coordinates. -/
def standardY5 : Generator where
  color := -2
  weak := 3
  singlet := 0
  traceless := by norm_num

/-- A second independent traceless block-scalar generator. -/
def extraX : Generator where
  color := 1
  weak := 1
  singlet := -5
  traceless := by norm_num

/-- The explicit linear combination `a*Y5 + b*X`. -/
def combine (a b : ℚ) : Generator where
  color := -2 * a + b
  weak := 3 * a + b
  singlet := -5 * b
  traceless := by ring

def standardCoefficient (Y : Generator) : ℚ :=
  (Y.weak - Y.color) / 5

def extraCoefficient (Y : Generator) : ℚ :=
  -Y.singlet / 5

/-- Every traceless block-scalar generator has the advertised two-parameter
form. -/
theorem combine_coefficients (Y : Generator) :
    combine (standardCoefficient Y) (extraCoefficient Y) = Y := by
  ext <;> dsimp [combine, standardCoefficient, extraCoefficient] <;>
    linarith [Y.traceless]

theorem standardCoefficient_combine (a b : ℚ) :
    standardCoefficient (combine a b) = a := by
  simp [standardCoefficient, combine]
  ring

theorem extraCoefficient_combine (a b : ℚ) :
    extraCoefficient (combine a b) = b := by
  simp [extraCoefficient, combine]

/-- The two coefficients are unique. -/
theorem combine_injective :
    Function.Injective (fun p : ℚ × ℚ => combine p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · simpa only [standardCoefficient_combine] using
      congrArg standardCoefficient h
  · simpa only [extraCoefficient_combine] using
      congrArg extraCoefficient h

/-- Equivalence between the rank-two coefficient space and the traceless
block-scalar generators. -/
def coefficientsEquiv : (ℚ × ℚ) ≃ Generator where
  toFun p := combine p.1 p.2
  invFun Y := (standardCoefficient Y, extraCoefficient Y)
  left_inv p := by
    apply Prod.ext
    · exact standardCoefficient_combine p.1 p.2
    · exact extraCoefficient_combine p.1 p.2
  right_inv := combine_coefficients

end HyperchargeCentralizer
end GUT
