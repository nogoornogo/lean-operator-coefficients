import GUT.SU6.Characters.NormalizedLaurent
import GUT.SU6.Characters.SignedWeylTransposition
import Mathlib.Tactic

open Math

/-!
# The color-neutral hypercharge branch

The primitive color-neutral centralizer cocharacter has defining weights
`(0,0,0,1,1,-2)`.  Its maximal Standard Model torus is therefore the
codimension-one diagonal subtorus cut out by

`x1 * x2 * x3 = 1`.

The remaining coordinates `x4,x5,x6` also have product one, so their `S_3`
permutations normalize this torus.  This file uses the transposition `(5 6)`.
It constructs its signed representative in `SU(6)`, proves that every finite
virtual `SU(6)` restricted character is fixed by the induced action, and shows
that the one-generation Standard Model chiral character is not fixed.

Thus the color-neutral arithmetic candidate is excluded at the same
function-level character scope as the flipped-branch obstruction.  The
separate hypercharge character rigidity problem of proving that an exact SM-only hypercharge embedding has
some neutral defining block is not asserted here.
-/

namespace GUT
namespace ColorNeutralBranch

noncomputable section

abbrev I6 := WeylMatrix.I6
abbrev SU6 := ActualRestriction.SU6
abbrev ActualSU6Representation := VirtualRestriction.ActualSU6Representation
abbrev FiniteVirtualSU6Representation :=
  VirtualRestriction.FiniteVirtualSU6Representation
abbrev Exp := Flipped.Exp
abbrev Poly := Flipped.Normalized.Poly

def i5 : I6 := 4
def i6 : I6 := 5

theorem i5_ne_i6 : i5 ≠ i6 := by decide

def coordinateSwap56 : Equiv.Perm I6 :=
  SignedWeylTransposition.transposition i5 i6

@[simp]
theorem coordinateSwap56_symm : coordinateSwap56.symm = coordinateSwap56 := by
  simp [coordinateSwap56]

def signedSwap56SU : Matrix.specialUnitaryGroup I6 ℂ :=
  SignedWeylTransposition.signedTranspositionSU i5 i6 i5_ne_i6

theorem signedSwap56SU_conj_diagonal (d : I6 → ℂ) :
    ((signedSwap56SU : Matrix.specialUnitaryGroup I6 ℂ) :
          Matrix I6 I6 ℂ) *
        Matrix.diagonal d *
        ((signedSwap56SU⁻¹ : Matrix.specialUnitaryGroup I6 ℂ) :
          Matrix I6 I6 ℂ) =
      Matrix.diagonal (d ∘ coordinateSwap56) := by
  exact SignedWeylTransposition.signedTranspositionSU_conj_diagonal
    i5 i6 i5_ne_i6 d

/-!
## The actual color-neutral diagonal torus
-/

structure DiagonalPoint where
  toDiagonal : ActualRestriction.DiagonalSU6Point
  color_relation :
    toDiagonal.coords 0 * toDiagonal.coords 1 * toDiagonal.coords 2 = 1

namespace DiagonalPoint

def coords (t : DiagonalPoint) : I6 → ℂ :=
  t.toDiagonal.coords

theorem det_product (t : DiagonalPoint) : ∏ i, t.coords i = 1 := by
  have hdet : (Matrix.diagonal t.toDiagonal.coords).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp t.toDiagonal.mem).2
  simpa [coords, Matrix.det_diagonal] using hdet

theorem coord_ne_zero (t : DiagonalPoint) (i : I6) : t.coords i ≠ 0 := by
  have hprod : (∏ j, t.coords j) ≠ 0 := by
    rw [t.det_product]
    norm_num
  rw [Finset.prod_ne_zero_iff] at hprod
  exact hprod i (Finset.mem_univ i)

def coordUnit (t : DiagonalPoint) (i : I6) : ℂˣ :=
  Units.mk0 (t.coords i) (t.coord_ne_zero i)

def swap56 (t : DiagonalPoint) : DiagonalPoint where
  toDiagonal := {
    coords := t.coords ∘ coordinateSwap56
    mem := by
      let g : SU6 := signedSwap56SU * t.toDiagonal.toSU6 * signedSwap56SU⁻¹
      have hg : ((g : SU6) : Matrix I6 I6 ℂ) =
          Matrix.diagonal (t.coords ∘ coordinateSwap56) := by
        change
          ((signedSwap56SU : Matrix.specialUnitaryGroup I6 ℂ) :
                Matrix I6 I6 ℂ) *
              Matrix.diagonal t.toDiagonal.coords *
              ((signedSwap56SU⁻¹ : Matrix.specialUnitaryGroup I6 ℂ) :
                Matrix I6 I6 ℂ) =
            Matrix.diagonal (t.toDiagonal.coords ∘ coordinateSwap56)
        exact signedSwap56SU_conj_diagonal t.toDiagonal.coords
      rw [← hg]
      exact SetLike.coe_mem g
  }
  color_relation := by
    change
      t.coords (coordinateSwap56 0) *
          t.coords (coordinateSwap56 1) *
        t.coords (coordinateSwap56 2) = 1
    have h0 : coordinateSwap56 0 = 0 := by decide
    have h1 : coordinateSwap56 1 = 1 := by decide
    have h2 : coordinateSwap56 2 = 2 := by decide
    simpa [coords, h0, h1, h2] using t.color_relation

theorem toSU6_swap56_eq_conj (t : DiagonalPoint) :
    (swap56 t).toDiagonal.toSU6 =
      signedSwap56SU * t.toDiagonal.toSU6 * signedSwap56SU⁻¹ := by
  apply Subtype.ext
  change Matrix.diagonal (t.coords ∘ coordinateSwap56) =
    ((signedSwap56SU : Matrix.specialUnitaryGroup I6 ℂ) :
          Matrix I6 I6 ℂ) *
      Matrix.diagonal t.toDiagonal.coords *
      ((signedSwap56SU⁻¹ : Matrix.specialUnitaryGroup I6 ℂ) :
        Matrix I6 I6 ℂ)
  exact (signedSwap56SU_conj_diagonal t.toDiagonal.coords).symm

theorem coord2_eq_inv_colorProduct (t : DiagonalPoint) :
    t.coords 2 = (t.coords 0 * t.coords 1)⁻¹ := by
  have hcolor : t.coords 0 * t.coords 1 * t.coords 2 = 1 := by
    simpa [coords] using t.color_relation
  exact eq_inv_of_mul_eq_one_right hcolor

theorem coord5_eq_inv_tailProduct (t : DiagonalPoint) :
    t.coords 5 = (t.coords 3 * t.coords 4)⁻¹ := by
  have hdet := t.det_product
  rw [Fin.prod_univ_six] at hdet
  have hcolor :
      t.coords 0 * t.coords 1 * t.coords 2 = 1 := by
    simpa [coords] using t.color_relation
  have htail : t.coords 3 * t.coords 4 * t.coords 5 = 1 := by
    calc
      t.coords 3 * t.coords 4 * t.coords 5 =
          (t.coords 0 * t.coords 1 * t.coords 2) *
            (t.coords 3 * t.coords 4 * t.coords 5) := by
              rw [hcolor]
              simp
      _ = t.coords 0 * t.coords 1 * t.coords 2 *
          t.coords 3 * t.coords 4 * t.coords 5 := by ring
      _ = 1 := hdet
  exact eq_inv_of_mul_eq_one_right htail

def toAlgebraicTorusPoint (t : DiagonalPoint) :
    Flipped.AlgebraicTorusPoint where
  z1 := t.coordUnit 0
  z2 := t.coordUnit 1
  z3 := t.coordUnit 3
  z4 := t.coordUnit 4

theorem coordUnit5_eq_inv_tailProduct (t : DiagonalPoint) :
    t.coordUnit 5 =
      (t.toAlgebraicTorusPoint.z3 * t.toAlgebraicTorusPoint.z4)⁻¹ := by
  apply Units.ext
  simp [coordUnit, toAlgebraicTorusPoint, coord5_eq_inv_tailProduct]

end DiagonalPoint

namespace AlgebraicTorusPoint

/-- The `(5 6)` action after eliminating
`x6 = (x4*x5)^-1`. -/
def swap56 (x : Flipped.AlgebraicTorusPoint) :
    Flipped.AlgebraicTorusPoint where
  z1 := x.z1
  z2 := x.z2
  z3 := x.z3
  z4 := (x.z3 * x.z4)⁻¹

theorem swap56_involutive (x : Flipped.AlgebraicTorusPoint) :
    swap56 (swap56 x) = x := by
  apply Flipped.AlgebraicTorusPoint.ext <;> simp [swap56]

end AlgebraicTorusPoint

theorem DiagonalPoint.toAlgebraicTorusPoint_swap56 (t : DiagonalPoint) :
    (DiagonalPoint.swap56 t).toAlgebraicTorusPoint =
      AlgebraicTorusPoint.swap56 t.toAlgebraicTorusPoint := by
  apply Flipped.AlgebraicTorusPoint.ext
  · apply Units.ext
    have h : coordinateSwap56 0 = 0 := by decide
    simp [DiagonalPoint.toAlgebraicTorusPoint, DiagonalPoint.coordUnit,
      DiagonalPoint.coords, DiagonalPoint.swap56,
      AlgebraicTorusPoint.swap56, h]
  · apply Units.ext
    have h : coordinateSwap56 1 = 1 := by decide
    simp [DiagonalPoint.toAlgebraicTorusPoint, DiagonalPoint.coordUnit,
      DiagonalPoint.coords, DiagonalPoint.swap56,
      AlgebraicTorusPoint.swap56, h]
  · apply Units.ext
    have h : coordinateSwap56 3 = 3 := by decide
    simp [DiagonalPoint.toAlgebraicTorusPoint, DiagonalPoint.coordUnit,
      DiagonalPoint.coords, DiagonalPoint.swap56,
      AlgebraicTorusPoint.swap56, h]
  · simpa [DiagonalPoint.toAlgebraicTorusPoint,
      DiagonalPoint.coordUnit, DiagonalPoint.coords,
      DiagonalPoint.swap56, AlgebraicTorusPoint.swap56,
      (by decide : coordinateSwap56 4 = 5)]
      using t.coordUnit5_eq_inv_tailProduct

/-!
## Normalized Laurent action
-/

def swap56Exp (e : Exp) : Exp :=
  { z1 := e.z1
    z2 := e.z2
    z3 := e.z3 - e.z4
    z4 := -e.z4 }

@[simp]
theorem swap56Exp_involutive (e : Exp) : swap56Exp (swap56Exp e) = e := by
  cases e
  simp [swap56Exp]

theorem swap56Exp_injective : Function.Injective swap56Exp := by
  intro e f h
  have h' := congrArg swap56Exp h
  simpa using h'

theorem evalUnit_swap56Exp (e : Exp) (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Exp.evalUnit (swap56Exp e) x =
      Flipped.Exp.evalUnit e (AlgebraicTorusPoint.swap56 x) := by
  cases e with
  | mk a b c d =>
    change
      x.z1 ^ a * x.z2 ^ b * x.z3 ^ (c - d) * x.z4 ^ (-d) =
        x.z1 ^ a * x.z2 ^ b * x.z3 ^ c * ((x.z3 * x.z4)⁻¹) ^ d
    simp only [zpow_sub, zpow_neg, inv_zpow', mul_zpow, mul_inv_rev]
    simp only [mul_assoc, mul_comm]

theorem eval_swap56Exp (e : Exp) (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Exp.eval (swap56Exp e) x =
      Flipped.Exp.eval e (AlgebraicTorusPoint.swap56 x) := by
  exact congrArg Units.val (evalUnit_swap56Exp e x)

def swap56 (p : Poly) : Poly :=
  Finsupp.mapDomain swap56Exp p

theorem swap56_add (p q : Poly) : swap56 (p + q) = swap56 p + swap56 q :=
  Finsupp.mapDomain_add

theorem swap56_zscale (n : ℤ) (p : Poly) :
    swap56 (Flipped.Normalized.zscale n p) =
      Flipped.Normalized.zscale n (swap56 p) := by
  simpa [swap56, Flipped.Normalized.zscale] using
    (Finsupp.mapDomain_mapRange swap56Exp p (fun c : ℤ => n * c)
      (by simp) (by intro x y; ring))

theorem eval_swap56 (p : Poly) (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval (swap56 p) x =
      Flipped.Normalized.eval p (AlgebraicTorusPoint.swap56 x) := by
  rw [Flipped.Normalized.eval, swap56, Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro e _he
    simp [eval_swap56Exp]
  · intro e
    simp
  · intro e a b
    rw [Int.cast_add]
    ring

theorem eval_neg (p : Poly) (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval (-p) x =
      -Flipped.Normalized.eval p x := by
  apply eq_neg_of_add_eq_zero_left
  rw [← Flipped.Normalized.eval_add, neg_add_cancel,
    Flipped.Normalized.eval_zero]

/-!
## The color-neutral Standard Model character
-/

def mon (z1 z2 z3 z4 coeff : ℤ) : Poly :=
  Flipped.Normalized.mon z1 z2 z3 z4 coeff

/-- `Q-Q*` for color weights
`z1,z2,(z1*z2)^-1` and weak-hypercharge weights `z3,z4`. -/
def qCharacter : Poly :=
    mon 1 0 1 0 1 + mon 1 0 0 1 1
  + mon 0 1 1 0 1 + mon 0 1 0 1 1
  + mon (-1) (-1) 1 0 1 + mon (-1) (-1) 0 1 1
  + mon (-1) 0 (-1) 0 (-1) + mon (-1) 0 0 (-1) (-1)
  + mon 0 (-1) (-1) 0 (-1) + mon 0 (-1) 0 (-1) (-1)
  + mon 1 1 (-1) 0 (-1) + mon 1 1 0 (-1) (-1)

/-- `u^c-(u^c)*` at six-times-hypercharge `-4`. -/
def upCharacter : Poly :=
    mon (-1) 0 (-2) (-2) 1
  + mon 0 (-1) (-2) (-2) 1
  + mon 1 1 (-2) (-2) 1
  + mon 1 0 2 2 (-1)
  + mon 0 1 2 2 (-1)
  + mon (-1) (-1) 2 2 (-1)

/-- `d^c-(d^c)*` at six-times-hypercharge `2`. -/
def downCharacter : Poly :=
    mon (-1) 0 1 1 1
  + mon 0 (-1) 1 1 1
  + mon 1 1 1 1 1
  + mon 1 0 (-1) (-1) (-1)
  + mon 0 1 (-1) (-1) (-1)
  + mon (-1) (-1) (-1) (-1) (-1)

/-- `L-L*` at six-times-hypercharge `-3`. -/
def leptonCharacter : Poly :=
    mon 0 0 (-1) (-2) 1
  + mon 0 0 (-2) (-1) 1
  + mon 0 0 1 2 (-1)
  + mon 0 0 2 1 (-1)

/-- `e^c-(e^c)*` at six-times-hypercharge `6`. -/
def electronCharacter : Poly :=
  mon 0 0 3 3 1 + mon 0 0 (-3) (-3) (-1)

/-- One generation of the chiral Standard Model character in the
color-neutral ambient-coordinate model. -/
def colorNeutralSMCharacter : Poly :=
  qCharacter + upCharacter + downCharacter +
    leptonCharacter + electronCharacter

def colorTripletValue (x : Flipped.AlgebraicTorusPoint) : ℂ :=
  (x.z1 : ℂ) + x.z2 + ((x.z1 : ℂ) * x.z2)⁻¹

def colorAntiTripletValue (x : Flipped.AlgebraicTorusPoint) : ℂ :=
  (x.z1 : ℂ)⁻¹ + (x.z2 : ℂ)⁻¹ + (x.z1 : ℂ) * x.z2

/-- Evaluation of the quark-doublet chiral pair in ambient coordinates. -/
theorem qCharacter_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval qCharacter x =
      colorTripletValue x * ((x.z3 : ℂ) + x.z4) -
        colorAntiTripletValue x * ((x.z3 : ℂ)⁻¹ + (x.z4 : ℂ)⁻¹) := by
  simp [qCharacter, colorTripletValue, colorAntiTripletValue, mon,
    Flipped.Normalized.mon, Flipped.Normalized.eval_add,
    Flipped.Normalized.eval_single, Flipped.Exp.eval, Flipped.Exp.evalUnit,
    eval_neg]
  ring

/-- Evaluation of the up-antiquark chiral pair. -/
theorem upCharacter_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval upCharacter x =
      colorAntiTripletValue x *
          ((x.z3 : ℂ)⁻¹ ^ 2 * (x.z4 : ℂ)⁻¹ ^ 2) -
        colorTripletValue x * ((x.z3 : ℂ) ^ 2 * (x.z4 : ℂ) ^ 2) := by
  simp [upCharacter, colorTripletValue, colorAntiTripletValue, mon,
    Flipped.Normalized.mon, Flipped.Normalized.eval_add,
    Flipped.Normalized.eval_single, Flipped.Exp.eval, Flipped.Exp.evalUnit,
    eval_neg, pow_succ]
  ring

/-- Evaluation of the down-antiquark chiral pair. -/
theorem downCharacter_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval downCharacter x =
      colorAntiTripletValue x * ((x.z3 : ℂ) * x.z4) -
        colorTripletValue x * ((x.z3 : ℂ)⁻¹ * (x.z4 : ℂ)⁻¹) := by
  simp [downCharacter, colorTripletValue, colorAntiTripletValue, mon,
    Flipped.Normalized.mon, Flipped.Normalized.eval_add,
    Flipped.Normalized.eval_single, Flipped.Exp.eval, Flipped.Exp.evalUnit,
    eval_neg]
  ring

/-- Evaluation of the lepton-doublet chiral pair. -/
theorem leptonCharacter_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval leptonCharacter x =
      (x.z3 : ℂ)⁻¹ * (x.z4 : ℂ)⁻¹ ^ 2 +
        (x.z3 : ℂ)⁻¹ ^ 2 * (x.z4 : ℂ)⁻¹ -
        ((x.z3 : ℂ) * (x.z4 : ℂ) ^ 2 +
          (x.z3 : ℂ) ^ 2 * x.z4) := by
  simp [leptonCharacter, mon, Flipped.Normalized.mon,
    Flipped.Normalized.eval_add, Flipped.Normalized.eval_single,
    Flipped.Exp.eval, Flipped.Exp.evalUnit, eval_neg, pow_succ]
  ring

/-- Evaluation of the charged-antilepton chiral pair. -/
theorem electronCharacter_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval electronCharacter x =
      (x.z3 : ℂ) ^ 3 * (x.z4 : ℂ) ^ 3 -
        (x.z3 : ℂ)⁻¹ ^ 3 * (x.z4 : ℂ)⁻¹ ^ 3 := by
  simp [electronCharacter, mon, Flipped.Normalized.mon,
    Flipped.Normalized.eval_add, Flipped.Normalized.eval_single,
    Flipped.Exp.eval, Flipped.Exp.evalUnit, eval_neg, pow_succ]
  ring

/-- The canonical polynomial evaluates to the sum of the five Standard Model
chiral field-pair characters. -/
theorem colorNeutralSMCharacter_eval (x : Flipped.AlgebraicTorusPoint) :
    Flipped.Normalized.eval colorNeutralSMCharacter x =
      Flipped.Normalized.eval qCharacter x +
        Flipped.Normalized.eval upCharacter x +
        Flipped.Normalized.eval downCharacter x +
        Flipped.Normalized.eval leptonCharacter x +
        Flipped.Normalized.eval electronCharacter x := by
  simp [colorNeutralSMCharacter, Flipped.Normalized.eval_add,
    add_assoc]

def colorNeutralWitnessExp : Exp :=
  { z1 := 1, z2 := 0, z3 := 0, z4 := 1 }

theorem colorNeutralSMCharacter_coeff_witness :
    colorNeutralSMCharacter colorNeutralWitnessExp = 1 := by
  norm_num [colorNeutralSMCharacter, qCharacter, upCharacter,
    downCharacter, leptonCharacter, electronCharacter,
    colorNeutralWitnessExp, mon, Flipped.Normalized.mon]

theorem swap56_colorNeutralSMCharacter_coeff_witness :
    swap56 colorNeutralSMCharacter colorNeutralWitnessExp = -1 := by
  rw [show colorNeutralWitnessExp =
      swap56Exp (swap56Exp colorNeutralWitnessExp) by
    simp [colorNeutralWitnessExp]]
  rw [swap56, Finsupp.mapDomain_apply_of_injective swap56Exp_injective]
  norm_num [colorNeutralSMCharacter, qCharacter, upCharacter,
    downCharacter, leptonCharacter, electronCharacter,
    colorNeutralWitnessExp, mon, Flipped.Normalized.mon, swap56Exp]

theorem swap56_colorNeutralSMCharacter_ne :
    swap56 colorNeutralSMCharacter ≠ colorNeutralSMCharacter := by
  intro h
  have hcoeff := congrArg (fun p : Poly => p colorNeutralWitnessExp) h
  rw [swap56_colorNeutralSMCharacter_coeff_witness,
    colorNeutralSMCharacter_coeff_witness] at hcoeff
  norm_num at hcoeff

def singletCharacter (coeff : ℤ) : Poly :=
  mon 0 0 0 0 coeff

theorem swap56_singletCharacter (coeff : ℤ) :
    swap56 (singletCharacter coeff) = singletCharacter coeff := by
  simp [swap56, singletCharacter, mon, Flipped.Normalized.mon, swap56Exp]

theorem swap56_add_fixed_ne {p q : Poly}
    (hp : swap56 p ≠ p) (hq : swap56 q = q) :
    swap56 (p + q) ≠ p + q := by
  intro h
  apply hp
  exact add_right_cancel <| calc
    swap56 p + q = swap56 p + swap56 q := by rw [hq]
    _ = swap56 (p + q) := (swap56_add p q).symm
    _ = p + q := h

theorem swap56_nonzero_generation_ne (n : ℤ) (hn : n ≠ 0) :
    swap56 (Flipped.Normalized.zscale n colorNeutralSMCharacter) ≠
      Flipped.Normalized.zscale n colorNeutralSMCharacter := by
  intro h
  rw [swap56_zscale] at h
  have hcoeff := congrArg (fun p : Poly => p colorNeutralWitnessExp) h
  simp only [Flipped.Normalized.zscale_apply,
    swap56_colorNeutralSMCharacter_coeff_witness,
    colorNeutralSMCharacter_coeff_witness] at hcoeff
  apply hn
  omega

theorem swap56_nonzero_generation_add_singlets_ne
    (n : ℤ) (hn : n ≠ 0) (singlets : ℤ) :
    swap56
        (Flipped.Normalized.zscale n colorNeutralSMCharacter +
          singletCharacter singlets) ≠
      Flipped.Normalized.zscale n colorNeutralSMCharacter +
        singletCharacter singlets :=
  swap56_add_fixed_ne (swap56_nonzero_generation_ne n hn)
    (swap56_singletCharacter singlets)

/-!
## Faithful evaluation on the actual compact torus
-/

def unitAddTorusCoord (x : UnitAddTorus (Fin 4)) (i : Fin 4) : Circle :=
  AddCircle.toCircle (x i)

def coordsOfUnitAddTorus (x : UnitAddTorus (Fin 4)) : I6 → ℂ :=
  ![(unitAddTorusCoord x 0 : ℂ),
    (unitAddTorusCoord x 1 : ℂ),
    ((((unitAddTorusCoord x 0) * (unitAddTorusCoord x 1))⁻¹ : Circle) : ℂ),
    (unitAddTorusCoord x 2 : ℂ),
    (unitAddTorusCoord x 3 : ℂ),
    ((((unitAddTorusCoord x 2) * (unitAddTorusCoord x 3))⁻¹ : Circle) : ℂ)]

theorem diagonal_coordsOfUnitAddTorus_mem_unitaryGroup
    (x : UnitAddTorus (Fin 4)) :
    Matrix.diagonal (coordsOfUnitAddTorus x) ∈
      Matrix.unitaryGroup I6 ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordsOfUnitAddTorus, unitAddTorusCoord,
      FlippedTorus.FlippedDiagonalSU6Point.circle_star_eq_inv,
      mul_left_comm, mul_comm]

theorem determinant_coordsOfUnitAddTorus (x : UnitAddTorus (Fin 4)) :
    (Matrix.diagonal (coordsOfUnitAddTorus x) :
      Matrix I6 I6 ℂ).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_six]
  change
    (((unitAddTorusCoord x 0) * (unitAddTorusCoord x 1) *
        ((unitAddTorusCoord x 0) * (unitAddTorusCoord x 1))⁻¹ *
        (unitAddTorusCoord x 2) * (unitAddTorusCoord x 3) *
        ((unitAddTorusCoord x 2) * (unitAddTorusCoord x 3))⁻¹ : Circle) : ℂ) = 1
  simp [mul_assoc]

def ofUnitAddTorus (x : UnitAddTorus (Fin 4)) : DiagonalPoint where
  toDiagonal := {
    coords := coordsOfUnitAddTorus x
    mem := by
      rw [Matrix.mem_specialUnitaryGroup_iff]
      exact ⟨diagonal_coordsOfUnitAddTorus_mem_unitaryGroup x,
        determinant_coordsOfUnitAddTorus x⟩
  }
  color_relation := by
    change
      (((unitAddTorusCoord x 0) * (unitAddTorusCoord x 1) *
          ((unitAddTorusCoord x 0) * (unitAddTorusCoord x 1))⁻¹ : Circle) : ℂ) = 1
    simp

theorem toAlgebraicTorusPoint_ofUnitAddTorus (x : UnitAddTorus (Fin 4)) :
    (ofUnitAddTorus x).toAlgebraicTorusPoint =
      Flipped.AlgebraicTorusPoint.ofUnitAddTorus x := by
  apply Flipped.AlgebraicTorusPoint.ext <;>
    apply Units.ext <;>
    simp [ofUnitAddTorus, Flipped.AlgebraicTorusPoint.ofUnitAddTorus,
      DiagonalPoint.toAlgebraicTorusPoint, DiagonalPoint.coords,
      DiagonalPoint.coordUnit, coordsOfUnitAddTorus, unitAddTorusCoord]

def diagonalLaurentEval (p : Poly) (t : DiagonalPoint) : ℂ :=
  Flipped.Normalized.eval p t.toAlgebraicTorusPoint

theorem diagonalLaurentFaithful :
    ∀ p q : Poly,
      (∀ t : DiagonalPoint,
        diagonalLaurentEval p t = diagonalLaurentEval q t) → p = q := by
  intro p q h
  apply Flipped.Normalized.evalUnitAddTorus_faithful
  intro x
  have hx := h (ofUnitAddTorus x)
  simpa [diagonalLaurentEval, toAlgebraicTorusPoint_ofUnitAddTorus,
    Flipped.Normalized.eval_ofUnitAddTorus] using hx

theorem diagonalLaurentEval_swap56 (p : Poly) (t : DiagonalPoint) :
    diagonalLaurentEval (swap56 p) t =
      diagonalLaurentEval p (t.swap56) := by
  unfold diagonalLaurentEval
  rw [eval_swap56, ← t.toAlgebraicTorusPoint_swap56]

/-!
## Finite virtual character exclusion
-/

def restrictedCharacter :
    FiniteVirtualSU6Representation → DiagonalPoint → ℂ
  | [], _ => 0
  | s :: ss, t =>
      (s.coeff : ℂ) * s.rep.rho.character t.toDiagonal.toSU6 +
        restrictedCharacter ss t

theorem restrictedCharacter_swap56_fixed
    (chi : FiniteVirtualSU6Representation) (t : DiagonalPoint) :
    restrictedCharacter chi t.swap56 = restrictedCharacter chi t := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      simp only [restrictedCharacter]
      rw [t.toSU6_swap56_eq_conj]
      rw [MathlibBridge.su6_representation_character_conj]
      rw [ih]

theorem no_restrictedCharacter_eq_diagonalLaurentEval_of_not_fixed
    (p : Poly) (hp : swap56 p ≠ p) :
    ¬ ∃ chi : FiniteVirtualSU6Representation,
      ∀ t : DiagonalPoint,
        restrictedCharacter chi t = diagonalLaurentEval p t := by
  intro h
  rcases h with ⟨chi, hchi⟩
  apply hp
  apply diagonalLaurentFaithful
  intro t
  calc
    diagonalLaurentEval (swap56 p) t =
        diagonalLaurentEval p t.swap56 := diagonalLaurentEval_swap56 p t
    _ = restrictedCharacter chi t.swap56 := (hchi t.swap56).symm
    _ = restrictedCharacter chi t := restrictedCharacter_swap56_fixed chi t
    _ = diagonalLaurentEval p t := hchi t

/-- The one-generation color-neutral SM character is not the restriction of
any finite virtual `SU(6)` character. -/
theorem no_colorNeutralSM_uplift :
    ¬ ∃ chi : FiniteVirtualSU6Representation,
      ∀ t : DiagonalPoint,
        restrictedCharacter chi t =
          diagonalLaurentEval colorNeutralSMCharacter t :=
  no_restrictedCharacter_eq_diagonalLaurentEval_of_not_fixed
    colorNeutralSMCharacter swap56_colorNeutralSMCharacter_ne

/-- The obstruction persists for any nonzero generation number and any
integer virtual multiplicity of gauge singlets. -/
theorem no_nonzero_generation_colorNeutralSM_add_singlets_uplift
    (n : ℤ) (hn : n ≠ 0) (singlets : ℤ) :
    ¬ ∃ chi : FiniteVirtualSU6Representation,
      ∀ t : DiagonalPoint,
        restrictedCharacter chi t =
          diagonalLaurentEval
            (Flipped.Normalized.zscale n colorNeutralSMCharacter +
              singletCharacter singlets) t :=
  no_restrictedCharacter_eq_diagonalLaurentEval_of_not_fixed _
    (swap56_nonzero_generation_add_singlets_ne n hn singlets)

end


end ColorNeutralBranch
end GUT
