import GUT.SU6.Characters.WeightTheory
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open Math

/-!
# Normalized Laurent model

The first Laurent model in `GUT.Flipped` deliberately exposes the
concrete list of terms.  That is convenient for computation, but too syntactic
for a global faithfulness statement: duplicate monomials and zero coefficients
can evaluate to the same function.

This file introduces the normalized model `Exp →₀ ℤ`.  The support is keyed by
exponents, so equal exponents are combined by construction.  We then prove
faithfulness on the algebraic torus by Dedekind linear independence of distinct
monoid characters.
-/

namespace GUT
namespace Flipped

noncomputable section

abbrev TorusVec := Fin 4 → ℂˣ

namespace AlgebraicTorusPoint

def toVec (x : AlgebraicTorusPoint) : TorusVec :=
  ![x.z1, x.z2, x.z3, x.z4]

def ofVec (x : TorusVec) : AlgebraicTorusPoint where
  z1 := x 0
  z2 := x 1
  z3 := x 2
  z4 := x 3

@[simp]
theorem toVec_ofVec (x : TorusVec) : (ofVec x).toVec = x := by
  funext i
  fin_cases i <;> rfl

def ofUnitAddTorus (x : UnitAddTorus (Fin 4)) : AlgebraicTorusPoint where
  z1 := Circle.toUnits (AddCircle.toCircle (x 0))
  z2 := Circle.toUnits (AddCircle.toCircle (x 1))
  z3 := Circle.toUnits (AddCircle.toCircle (x 2))
  z4 := Circle.toUnits (AddCircle.toCircle (x 3))

end AlgebraicTorusPoint

namespace Exp

def evalUnitVec (e : Exp) (x : TorusVec) : ℂˣ :=
  x 0 ^ e.z1 * x 1 ^ e.z2 * x 2 ^ e.z3 * x 3 ^ e.z4

def evalUnitVecHom (e : Exp) : TorusVec →* ℂˣ where
  toFun := evalUnitVec e
  map_one' := by
    cases e
    simp [evalUnitVec]
  map_mul' := by
    intro x y
    cases e
    simp [evalUnitVec, mul_zpow, mul_assoc, mul_left_comm]

def evalVecMonoidHom (e : Exp) : TorusVec →* ℂ :=
  (Units.coeHom ℂ).comp (evalUnitVecHom e)

theorem eval_eq_evalVecMonoidHom (e : Exp) (x : AlgebraicTorusPoint) :
    e.eval x = Exp.evalVecMonoidHom e x.toVec := by
  cases e
  simp [Exp.eval, Exp.evalUnit, Exp.evalVecMonoidHom, Exp.evalUnitVecHom, Exp.evalUnitVec,
    AlgebraicTorusPoint.toVec]

def twoUnit : ℂˣ :=
  Units.mk0 (2 : ℂ) (by norm_num)

def basisPoint (i : Fin 4) : TorusVec :=
  fun j => if j = i then twoUnit else 1

theorem complex_two_zpow_injective :
    Function.Injective fun n : ℤ => (2 : ℂ) ^ n := by
  intro m n h
  apply zpow_right_injective₀ (a := (2 : ℝ)) (by norm_num) (by norm_num)
  apply Complex.ofReal_injective
  simpa [Complex.ofReal_zpow] using h

theorem evalVecMonoidHom_injective :
    Function.Injective evalVecMonoidHom := by
  intro e f h
  cases e with
  | mk a b c d =>
  cases f with
  | mk aa bb cc dd =>
  have h0 : (2 : ℂ) ^ a = (2 : ℂ) ^ aa := by
    have hh := congrArg (fun φ : TorusVec →* ℂ => φ (basisPoint 0)) h
    simpa [evalVecMonoidHom, evalUnitVecHom, evalUnitVec, basisPoint, twoUnit] using hh
  have h1 : (2 : ℂ) ^ b = (2 : ℂ) ^ bb := by
    have hh := congrArg (fun φ : TorusVec →* ℂ => φ (basisPoint 1)) h
    simpa [evalVecMonoidHom, evalUnitVecHom, evalUnitVec, basisPoint, twoUnit] using hh
  have h2 : (2 : ℂ) ^ c = (2 : ℂ) ^ cc := by
    have hh := congrArg (fun φ : TorusVec →* ℂ => φ (basisPoint 2)) h
    simpa [evalVecMonoidHom, evalUnitVecHom, evalUnitVec, basisPoint, twoUnit] using hh
  have h3 : (2 : ℂ) ^ d = (2 : ℂ) ^ dd := by
    have hh := congrArg (fun φ : TorusVec →* ℂ => φ (basisPoint 3)) h
    simpa [evalVecMonoidHom, evalUnitVecHom, evalUnitVec, basisPoint, twoUnit] using hh
  have ha := complex_two_zpow_injective h0
  have hb := complex_two_zpow_injective h1
  have hc := complex_two_zpow_injective h2
  have hd := complex_two_zpow_injective h3
  subst aa
  subst bb
  subst cc
  subst dd
  rfl

theorem linearIndependent_evalVecMonoidHom :
    LinearIndependent ℂ (fun e : Exp => (evalVecMonoidHom e : TorusVec → ℂ)) := by
  exact (linearIndependent_monoidHom TorusVec ℂ).comp
    evalVecMonoidHom evalVecMonoidHom_injective

def toFourierIndex (e : Exp) : Fin 4 → ℤ :=
  ![e.z1, e.z2, e.z3, e.z4]

theorem toFourierIndex_injective :
    Function.Injective toFourierIndex := by
  intro e f h
  cases e with
  | mk a b c d =>
  cases f with
  | mk aa bb cc dd =>
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp [toFourierIndex] at h0 h1 h2 h3
  subst aa
  subst bb
  subst cc
  subst dd
  rfl

theorem mFourier_injective :
    Function.Injective (UnitAddTorus.mFourier (d := Fin 4)) := by
  intro m n h
  have hLp :
      UnitAddTorus.mFourierLp (d := Fin 4) 2 m =
        UnitAddTorus.mFourierLp (d := Fin 4) 2 n := by
    dsimp [UnitAddTorus.mFourierLp]
    rw [h]
  exact (UnitAddTorus.orthonormal_mFourier (d := Fin 4)).linearIndependent.injective hLp

def evalUnitAddTorusMonoidHom
    (e : Exp) : Multiplicative (UnitAddTorus (Fin 4)) →* ℂ where
  toFun x := UnitAddTorus.mFourier e.toFourierIndex (Multiplicative.toAdd x)
  map_one' := by
    simp [UnitAddTorus.mFourier]
  map_mul' := by
    intro x y
    simp [UnitAddTorus.mFourier, AddCircle.toCircle_add, Finset.prod_mul_distrib]

theorem eval_ofUnitAddTorus (e : Exp) (x : UnitAddTorus (Fin 4)) :
    e.eval (AlgebraicTorusPoint.ofUnitAddTorus x) =
      Exp.evalUnitAddTorusMonoidHom e (Multiplicative.ofAdd x) := by
  cases e
  simp [Exp.eval, Exp.evalUnit, AlgebraicTorusPoint.ofUnitAddTorus,
    Exp.evalUnitAddTorusMonoidHom, UnitAddTorus.mFourier, Exp.toFourierIndex,
    Fin.prod_univ_four, AddCircle.toCircle_zsmul]

theorem evalUnitAddTorusMonoidHom_injective :
    Function.Injective evalUnitAddTorusMonoidHom := by
  intro e f h
  apply toFourierIndex_injective
  apply mFourier_injective
  ext x
  have hh := congrArg
    (fun φ : Multiplicative (UnitAddTorus (Fin 4)) →* ℂ =>
      φ (Multiplicative.ofAdd x)) h
  change
    UnitAddTorus.mFourier e.toFourierIndex x =
      UnitAddTorus.mFourier f.toFourierIndex x
  change
    UnitAddTorus.mFourier e.toFourierIndex
        (Multiplicative.toAdd (Multiplicative.ofAdd x)) =
      UnitAddTorus.mFourier f.toFourierIndex
        (Multiplicative.toAdd (Multiplicative.ofAdd x)) at hh
  simpa using hh

theorem linearIndependent_evalUnitAddTorusMonoidHom :
    LinearIndependent ℂ
      (fun e : Exp =>
        (evalUnitAddTorusMonoidHom e :
          Multiplicative (UnitAddTorus (Fin 4)) → ℂ)) := by
  exact (linearIndependent_monoidHom
      (Multiplicative (UnitAddTorus (Fin 4))) ℂ).comp
    evalUnitAddTorusMonoidHom evalUnitAddTorusMonoidHom_injective

end Exp

theorem swap36Exp_involutive (e : Exp) :
    swap36Exp (swap36Exp e) = e := by
  cases e
  simp [swap36Exp]

theorem swap36Exp_injective :
    Function.Injective swap36Exp := by
  intro e f h
  have h' := congrArg swap36Exp h
  simpa [swap36Exp_involutive] using h'

namespace Normalized

abbrev Poly := Exp →₀ ℤ

def toComplex (p : Poly) : Exp →₀ ℂ :=
  Finsupp.mapRange (fun n : ℤ => (n : ℂ)) (by simp) p

@[simp]
theorem toComplex_apply (p : Poly) (e : Exp) :
    toComplex p e = (p e : ℂ) := by
  simp [toComplex]

def evalVec (p : Poly) (x : TorusVec) : ℂ :=
  p.sum fun e c => (c : ℂ) * Exp.evalVecMonoidHom e x

theorem evalVec_eq_linearCombination (p : Poly) :
    Finsupp.linearCombination ℂ
        (fun e : Exp => (Exp.evalVecMonoidHom e : TorusVec → ℂ))
        (toComplex p)
      =
    fun x => evalVec p x := by
  ext x
  rw [Finsupp.linearCombination_apply, toComplex, Finsupp.sum_mapRange_index]
  · simp [evalVec, Finsupp.sum, Pi.smul_apply, smul_eq_mul]
  · intro e
    simp

theorem evalVec_faithful :
    ∀ p q : Poly, (∀ x : TorusVec, evalVec p x = evalVec q x) → p = q := by
  intro p q h
  have hlin :
      Finsupp.linearCombination ℂ
          (fun e : Exp => (Exp.evalVecMonoidHom e : TorusVec → ℂ))
          (toComplex p)
        =
      Finsupp.linearCombination ℂ
          (fun e : Exp => (Exp.evalVecMonoidHom e : TorusVec → ℂ))
          (toComplex q) := by
    rw [evalVec_eq_linearCombination p, evalVec_eq_linearCombination q]
    funext x
    exact h x
  have hC : toComplex p = toComplex q :=
    Exp.linearIndependent_evalVecMonoidHom.finsuppLinearCombination_injective hlin
  ext e
  exact Int.cast_injective (α := ℂ) (by
    simpa [toComplex_apply] using congrArg (fun r : Exp →₀ ℂ => r e) hC)

def eval (p : Poly) (x : AlgebraicTorusPoint) : ℂ :=
  p.sum fun e c => (c : ℂ) * e.eval x

def evalUnitAddTorus (p : Poly) (x : UnitAddTorus (Fin 4)) : ℂ :=
  p.sum fun e c =>
    (c : ℂ) * Exp.evalUnitAddTorusMonoidHom e (Multiplicative.ofAdd x)

theorem eval_ofUnitAddTorus (p : Poly) (x : UnitAddTorus (Fin 4)) :
    eval p (AlgebraicTorusPoint.ofUnitAddTorus x) =
      evalUnitAddTorus p x := by
  apply Finsupp.sum_congr
  intro e _he
  simp [Exp.eval_ofUnitAddTorus]

theorem evalUnitAddTorus_eq_linearCombination (p : Poly) :
    Finsupp.linearCombination ℂ
        (fun e : Exp =>
          (Exp.evalUnitAddTorusMonoidHom e :
            Multiplicative (UnitAddTorus (Fin 4)) → ℂ))
        (toComplex p)
      =
    fun x => evalUnitAddTorus p (Multiplicative.toAdd x) := by
  ext x
  rw [Finsupp.linearCombination_apply, toComplex, Finsupp.sum_mapRange_index]
  · simp [evalUnitAddTorus, Finsupp.sum, Pi.smul_apply, smul_eq_mul]
  · intro e
    simp

theorem evalUnitAddTorus_faithful :
    ∀ p q : Poly,
      (∀ x : UnitAddTorus (Fin 4),
        evalUnitAddTorus p x = evalUnitAddTorus q x) → p = q := by
  intro p q h
  have hlin :
      Finsupp.linearCombination ℂ
          (fun e : Exp =>
            (Exp.evalUnitAddTorusMonoidHom e :
              Multiplicative (UnitAddTorus (Fin 4)) → ℂ))
          (toComplex p)
        =
      Finsupp.linearCombination ℂ
          (fun e : Exp =>
            (Exp.evalUnitAddTorusMonoidHom e :
              Multiplicative (UnitAddTorus (Fin 4)) → ℂ))
          (toComplex q) := by
    rw [evalUnitAddTorus_eq_linearCombination p,
      evalUnitAddTorus_eq_linearCombination q]
    funext x
    exact h (Multiplicative.toAdd x)
  have hC : toComplex p = toComplex q :=
    Exp.linearIndependent_evalUnitAddTorusMonoidHom.finsuppLinearCombination_injective
      hlin
  ext e
  exact Int.cast_injective (α := ℂ) (by
    simpa [toComplex_apply] using congrArg (fun r : Exp →₀ ℂ => r e) hC)

theorem eval_eq_evalVec (p : Poly) (x : AlgebraicTorusPoint) :
    eval p x = evalVec p x.toVec := by
  apply Finsupp.sum_congr
  intro e _he
  simp [Exp.eval_eq_evalVecMonoidHom]

theorem eval_faithful :
    ∀ p q : Poly, (∀ x : AlgebraicTorusPoint, eval p x = eval q x) → p = q := by
  intro p q h
  apply evalVec_faithful
  intro x
  have hx := h (AlgebraicTorusPoint.ofVec x)
  simpa [eval_eq_evalVec, AlgebraicTorusPoint.toVec_ofVec] using hx

theorem eval_zero (x : AlgebraicTorusPoint) :
    eval (0 : Poly) x = 0 := by
  simp [eval]

theorem eval_single (e : Exp) (c : ℤ) (x : AlgebraicTorusPoint) :
    eval (Finsupp.single e c : Poly) x = (c : ℂ) * e.eval x := by
  simp [eval]

theorem eval_add (p q : Poly) (x : AlgebraicTorusPoint) :
    eval (p + q) x = eval p x + eval q x := by
  rw [eval, eval, eval, Finsupp.sum_add_index]
  · intro e _he
    simp
  · intro e _he a b
    rw [Int.cast_add]
    ring

def zscale (n : ℤ) (p : Poly) : Poly :=
  Finsupp.mapRange (fun c : ℤ => n * c) (by simp) p

@[simp]
theorem zscale_apply (n : ℤ) (p : Poly) (e : Exp) :
    zscale n p e = n * p e := by
  simp [zscale]

theorem eval_zscale (n : ℤ) (p : Poly) (x : AlgebraicTorusPoint) :
    eval (zscale n p) x = (n : ℂ) * eval p x := by
  rw [eval, zscale, Finsupp.sum_mapRange_index]
  · calc
      p.sum (fun e c => ((n * c : ℤ) : ℂ) * e.eval x)
          = p.sum (fun e c => (n : ℂ) * ((c : ℂ) * e.eval x)) := by
            apply Finsupp.sum_congr
            intro e _he
            rw [Int.cast_mul]
            ring
      _ = (n : ℂ) * p.sum (fun e c => (c : ℂ) * e.eval x) := by
            simpa using
              (Finsupp.mul_sum (n : ℂ) p
                (f := fun e c => (c : ℂ) * e.eval x)).symm
  · intro e
    simp

def swap36 (p : Poly) : Poly :=
  Finsupp.mapDomain swap36Exp p

theorem swap36_add (p q : Poly) :
    swap36 (p + q) = swap36 p + swap36 q := by
  exact Finsupp.mapDomain_add

theorem swap36_zscale (n : ℤ) (p : Poly) :
    swap36 (zscale n p) = zscale n (swap36 p) := by
  simpa [swap36, zscale] using
    (Finsupp.mapDomain_mapRange swap36Exp p (fun c : ℤ => n * c)
      (by simp) (by intro x y; ring))

theorem eval_swap36 (p : Poly) (x : AlgebraicTorusPoint) :
    eval (swap36 p) x = eval p x.swap36 := by
  rw [eval, swap36, Finsupp.sum_mapDomain_index]
  · apply Finsupp.sum_congr
    intro e _he
    simp [Exp.eval_swap36Exp]
  · intro e
    simp
  · intro e a b
    rw [Int.cast_add]
    ring

def ofTerms : List Term → Poly
  | [] => 0
  | t :: ts => Finsupp.single t.exp t.coeff + ofTerms ts

def ofListPoly (p : Flipped.Poly) : Poly :=
  ofTerms p.terms

theorem eval_ofTerms (terms : List Term) (x : AlgebraicTorusPoint) :
    eval (ofTerms terms) x = Flipped.Poly.evalTerms terms x := by
  induction terms with
  | nil => simp [ofTerms, eval_zero, Flipped.Poly.evalTerms]
  | cons t ts ih =>
      simp [ofTerms, eval_add, eval_single, Flipped.Poly.evalTerms,
        Term.eval, ih]

/-- Normalization from the legacy list syntax preserves Laurent evaluation. -/
theorem eval_ofListPoly (p : Flipped.Poly) (x : AlgebraicTorusPoint) :
    eval (ofListPoly p) x = p.eval x := by
  exact eval_ofTerms p.terms x

def ofRawCharacter : RawCharacter Exp → Poly
  | [] => 0
  | m :: ms => Finsupp.single m.exp m.coeff + ofRawCharacter ms

theorem eval_ofRawCharacter (χ : RawCharacter Exp) (x : AlgebraicTorusPoint) :
    eval (ofRawCharacter χ) x = χ.eval x := by
  induction χ with
  | nil =>
      simp [ofRawCharacter, RawCharacter.eval, eval_zero]
  | cons m ms ih =>
      cases m
      simp [ofRawCharacter, RawCharacter.eval, eval_add, eval_single, ih]

/-- The sorted legacy list used to certify the passage to the canonical model. -/
def legacyFlippedSMCharacterTerms : List Term :=
  [ { exp := { z1 := -2, z2 := -2, z3 := -2, z4 := 0 }, coeff := -1 }
  , { exp := { z1 := -2, z2 := -1, z3 := -1, z4 := 0 }, coeff := 1 }
  , { exp := { z1 := -1, z2 := -2, z3 := -1, z4 := 0 }, coeff := 1 }
  , { exp := { z1 := -1, z2 := -1, z3 := -2, z4 := 0 }, coeff := 1 }
  , { exp := { z1 := -1, z2 := -1, z3 := -1, z4 := -1 }, coeff := 1 }
  , { exp := { z1 := -1, z2 := -1, z3 := -1, z4 := 1 }, coeff := 1 }
  , { exp := { z1 := -1, z2 := -1, z3 := 0, z4 := 0 }, coeff := -1 }
  , { exp := { z1 := -1, z2 := 0, z3 := -1, z4 := 0 }, coeff := -1 }
  , { exp := { z1 := -1, z2 := 0, z3 := 0, z4 := -1 }, coeff := -1 }
  , { exp := { z1 := -1, z2 := 0, z3 := 0, z4 := 1 }, coeff := -1 }
  , { exp := { z1 := 0, z2 := -1, z3 := -1, z4 := 0 }, coeff := -1 }
  , { exp := { z1 := 0, z2 := -1, z3 := 0, z4 := -1 }, coeff := -1 }
  , { exp := { z1 := 0, z2 := -1, z3 := 0, z4 := 1 }, coeff := -1 }
  , { exp := { z1 := 0, z2 := 0, z3 := -1, z4 := -1 }, coeff := -1 }
  , { exp := { z1 := 0, z2 := 0, z3 := -1, z4 := 1 }, coeff := -1 }
  , { exp := { z1 := 0, z2 := 0, z3 := 1, z4 := -1 }, coeff := 1 }
  , { exp := { z1 := 0, z2 := 0, z3 := 1, z4 := 1 }, coeff := 1 }
  , { exp := { z1 := 0, z2 := 1, z3 := 0, z4 := -1 }, coeff := 1 }
  , { exp := { z1 := 0, z2 := 1, z3 := 0, z4 := 1 }, coeff := 1 }
  , { exp := { z1 := 0, z2 := 1, z3 := 1, z4 := 0 }, coeff := 1 }
  , { exp := { z1 := 1, z2 := 0, z3 := 0, z4 := -1 }, coeff := 1 }
  , { exp := { z1 := 1, z2 := 0, z3 := 0, z4 := 1 }, coeff := 1 }
  , { exp := { z1 := 1, z2 := 0, z3 := 1, z4 := 0 }, coeff := 1 }
  , { exp := { z1 := 1, z2 := 1, z3 := 0, z4 := 0 }, coeff := 1 }
  , { exp := { z1 := 1, z2 := 1, z3 := 1, z4 := -1 }, coeff := -1 }
  , { exp := { z1 := 1, z2 := 1, z3 := 1, z4 := 1 }, coeff := -1 }
  , { exp := { z1 := 1, z2 := 1, z3 := 2, z4 := 0 }, coeff := -1 }
  , { exp := { z1 := 1, z2 := 2, z3 := 1, z4 := 0 }, coeff := -1 }
  , { exp := { z1 := 2, z2 := 1, z3 := 1, z4 := 0 }, coeff := -1 }
  , { exp := { z1 := 2, z2 := 2, z3 := 2, z4 := 0 }, coeff := 1 } ]

theorem flippedSMCharacterExplicit_terms :
    Flipped.flippedSMCharacterExplicit.terms =
      legacyFlippedSMCharacterTerms := by
  decide

def legacyFlippedSMCharacter : Poly :=
  ofListPoly Flipped.flippedSMCharacter

def legacyFlippedSMCharacterExplicit : Poly :=
  ofListPoly Flipped.flippedSMCharacterExplicit

def mon (z1 z2 z3 z4 coeff : ℤ) : Poly :=
  Finsupp.single { z1 := z1, z2 := z2, z3 := z3, z4 := z4 } coeff

/-- The character of an integer virtual multiplicity of gauge singlets. -/
def singletCharacter (coeff : ℤ) : Poly :=
  mon 0 0 0 0 coeff

theorem swap36_singletCharacter (coeff : ℤ) :
    swap36 (singletCharacter coeff) = singletCharacter coeff := by
  simp [swap36, singletCharacter, mon, swap36Exp]

/- The normalized 30-term expansion of the flipped Standard Model character. -/
def flippedSMCharacter : Poly :=
    mon (-2) (-2) (-2) 0 (-1)
  + mon (-2) (-1) (-1) 0 1
  + mon (-1) (-2) (-1) 0 1
  + mon (-1) (-1) (-2) 0 1
  + mon (-1) (-1) (-1) (-1) 1
  + mon (-1) (-1) (-1) 1 1
  + mon (-1) (-1) 0 0 (-1)
  + mon (-1) 0 (-1) 0 (-1)
  + mon (-1) 0 0 (-1) (-1)
  + mon (-1) 0 0 1 (-1)
  + mon 0 (-1) (-1) 0 (-1)
  + mon 0 (-1) 0 (-1) (-1)
  + mon 0 (-1) 0 1 (-1)
  + mon 0 0 (-1) (-1) (-1)
  + mon 0 0 (-1) 1 (-1)
  + mon 0 0 1 (-1) 1
  + mon 0 0 1 1 1
  + mon 0 1 0 (-1) 1
  + mon 0 1 0 1 1
  + mon 0 1 1 0 1
  + mon 1 0 0 (-1) 1
  + mon 1 0 0 1 1
  + mon 1 0 1 0 1
  + mon 1 1 0 0 1
  + mon 1 1 1 (-1) (-1)
  + mon 1 1 1 1 (-1)
  + mon 1 1 2 0 (-1)
  + mon 1 2 1 0 (-1)
  + mon 2 1 1 0 (-1)
  + mon 2 2 2 0 1

def flippedSMCharacterExplicit : Poly :=
  flippedSMCharacter

/-- The explicit legacy SM character has the same canonical normalization. -/
theorem legacyFlippedSMCharacterExplicit_eq_flippedSMCharacterExplicit :
    legacyFlippedSMCharacterExplicit = flippedSMCharacterExplicit := by
  unfold legacyFlippedSMCharacterExplicit ofListPoly
  rw [flippedSMCharacterExplicit_terms]
  ext e
  simp [legacyFlippedSMCharacterTerms, ofTerms,
    flippedSMCharacterExplicit, flippedSMCharacter, mon]
  ring

/--
The canonical `Finsupp` target is exactly the normalization of the original
factored flipped-SM Laurent character.
-/
theorem legacyFlippedSMCharacter_eq_flippedSMCharacter :
    legacyFlippedSMCharacter = flippedSMCharacter := by
  unfold legacyFlippedSMCharacter
  rw [← Flipped.flippedSM_factorization]
  exact legacyFlippedSMCharacterExplicit_eq_flippedSMCharacterExplicit

def flippedSMWitnessExp : Exp :=
  { z1 := -2, z2 := -2, z3 := -2, z4 := 0 }

theorem flippedSMCharacter_coeff_witness :
    flippedSMCharacter flippedSMWitnessExp = -1 := by
  norm_num [flippedSMCharacter, flippedSMWitnessExp, mon]

theorem swap36_flippedSMCharacter_coeff_witness :
    swap36 flippedSMCharacter flippedSMWitnessExp = 0 := by
  rw [show flippedSMWitnessExp = swap36Exp (swap36Exp flippedSMWitnessExp) by
    simp [flippedSMWitnessExp, swap36Exp]]
  rw [swap36, Finsupp.mapDomain_apply_of_injective swap36Exp_injective]
  norm_num [flippedSMCharacter, flippedSMWitnessExp, mon, swap36Exp]

theorem swap36_flippedSMCharacter_ne :
    swap36 flippedSMCharacter ≠ flippedSMCharacter := by
  intro h
  have hcoeff := congrArg (fun p : Poly => p flippedSMWitnessExp) h
  rw [swap36_flippedSMCharacter_coeff_witness, flippedSMCharacter_coeff_witness] at hcoeff
  norm_num at hcoeff

theorem swap36_zscale_flippedSMCharacter_ne
    (n : ℤ) (hn : n ≠ 0) :
    swap36 (zscale n flippedSMCharacter) ≠
      zscale n flippedSMCharacter := by
  intro h
  rw [swap36_zscale] at h
  have hcoeff := congrArg (fun p : Poly => p flippedSMWitnessExp) h
  simp only [zscale_apply, swap36_flippedSMCharacter_coeff_witness,
    flippedSMCharacter_coeff_witness] at hcoeff
  apply hn
  omega

theorem swap36_add_fixed_ne
    {p q : Poly}
    (hp : swap36 p ≠ p)
    (hq : swap36 q = q) :
    swap36 (p + q) ≠ p + q := by
  intro h
  apply hp
  exact add_right_cancel <| calc
    swap36 p + q = swap36 p + swap36 q := by rw [hq]
    _ = swap36 (p + q) := (swap36_add p q).symm
    _ = p + q := h

theorem swap36_nonzero_generation_add_singlets_ne
    (n : ℤ) (hn : n ≠ 0) (singlets : ℤ) :
    swap36
        (zscale n flippedSMCharacter + singletCharacter singlets) ≠
      zscale n flippedSMCharacter + singletCharacter singlets :=
  swap36_add_fixed_ne
    (swap36_zscale_flippedSMCharacter_ne n hn)
    (swap36_singletCharacter singlets)

theorem flippedSMCharacterExplicit_coeff_witness :
    flippedSMCharacterExplicit flippedSMWitnessExp = -1 := by
  simpa [flippedSMCharacterExplicit] using flippedSMCharacter_coeff_witness

theorem swap36_flippedSMCharacterExplicit_coeff_witness :
    swap36 flippedSMCharacterExplicit flippedSMWitnessExp = 0 := by
  simpa [flippedSMCharacterExplicit] using swap36_flippedSMCharacter_coeff_witness

theorem swap36_flippedSMCharacterExplicit_ne :
    swap36 flippedSMCharacterExplicit ≠ flippedSMCharacterExplicit := by
  intro h
  have hcoeff := congrArg (fun p : Poly => p flippedSMWitnessExp) h
  rw [swap36_flippedSMCharacterExplicit_coeff_witness,
    flippedSMCharacterExplicit_coeff_witness] at hcoeff
  norm_num at hcoeff

end Normalized

end
end Flipped

namespace FlippedTorus
namespace FlippedDiagonalSU6Point

noncomputable section

def unitAddTorusCoord (x : UnitAddTorus (Fin 4)) (i : Fin 4) : Circle :=
  AddCircle.toCircle (x i)

def coordsOfUnitAddTorus (x : UnitAddTorus (Fin 4)) :
    WeylMatrix.I6 → ℂ :=
  ![(unitAddTorusCoord x 0 : ℂ),
    (unitAddTorusCoord x 1 : ℂ),
    (unitAddTorusCoord x 2 : ℂ),
    (unitAddTorusCoord x 3 : ℂ),
    (((unitAddTorusCoord x 3)⁻¹ : Circle) : ℂ),
    ((((unitAddTorusCoord x 0) *
        (unitAddTorusCoord x 1) *
        (unitAddTorusCoord x 2))⁻¹ : Circle) : ℂ)]

theorem circle_star_eq_inv (z : Circle) :
    star (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
  rw [Complex.star_def]
  exact (Circle.coe_inv_eq_conj z).symm

theorem circle_mul_star (z : Circle) :
    (z : ℂ) * star (z : ℂ) = 1 := by
  rw [circle_star_eq_inv]
  change ((z * z⁻¹ : Circle) : ℂ) = 1
  simp

theorem circle_inv_mul_star_inv (z : Circle) :
    (z : ℂ)⁻¹ * (star (z : ℂ))⁻¹ = 1 := by
  rw [circle_star_eq_inv]
  simp

theorem circle_det_identity (a b c d : Circle) :
    (a : ℂ) * (b : ℂ) * (c : ℂ) * (d : ℂ) *
        (((d)⁻¹ : Circle) : ℂ) *
        ((((a * b * c)⁻¹ : Circle) : ℂ)) = 1 := by
  change ((a * b * c * d * d⁻¹ * (a * b * c)⁻¹ : Circle) : ℂ) = 1
  simp [mul_assoc]

theorem circle_weak_identity (d : Circle) :
    (d : ℂ) * (((d)⁻¹ : Circle) : ℂ) = 1 := by
  change ((d * d⁻¹ : Circle) : ℂ) = 1
  simp

theorem diagonal_coordsOfUnitAddTorus_mem_unitaryGroup
    (x : UnitAddTorus (Fin 4)) :
    Matrix.diagonal (coordsOfUnitAddTorus x) ∈
      Matrix.unitaryGroup WeylMatrix.I6 ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordsOfUnitAddTorus, unitAddTorusCoord, circle_star_eq_inv,
      mul_assoc, mul_left_comm, mul_comm]

theorem determinant_coordsOfUnitAddTorus
    (x : UnitAddTorus (Fin 4)) :
    (Matrix.diagonal (coordsOfUnitAddTorus x) :
      Matrix WeylMatrix.I6 WeylMatrix.I6 ℂ).det = 1 := by
  rw [Matrix.det_diagonal, Fin.prod_univ_six]
  simpa [coordsOfUnitAddTorus, unitAddTorusCoord] using
    circle_det_identity (unitAddTorusCoord x 0) (unitAddTorusCoord x 1)
      (unitAddTorusCoord x 2) (unitAddTorusCoord x 3)

def ofUnitAddTorus (x : UnitAddTorus (Fin 4)) :
    FlippedDiagonalSU6Point where
  toDiagonal := {
    coords := coordsOfUnitAddTorus x
    mem := by
      rw [Matrix.mem_specialUnitaryGroup_iff]
      exact ⟨diagonal_coordsOfUnitAddTorus_mem_unitaryGroup x,
        determinant_coordsOfUnitAddTorus x⟩
  }
  weak_relation := by
    simp [coordsOfUnitAddTorus, unitAddTorusCoord]

theorem toAlgebraicTorusPoint_ofUnitAddTorus
    (x : UnitAddTorus (Fin 4)) :
    (ofUnitAddTorus x).toAlgebraicTorusPoint =
      Flipped.AlgebraicTorusPoint.ofUnitAddTorus x := by
  apply Flipped.AlgebraicTorusPoint.ext
  · apply Units.ext
    simp [ofUnitAddTorus, Flipped.AlgebraicTorusPoint.ofUnitAddTorus,
      toAlgebraicTorusPoint, coords, coordUnit, coordsOfUnitAddTorus,
      unitAddTorusCoord]
  · apply Units.ext
    simp [ofUnitAddTorus, Flipped.AlgebraicTorusPoint.ofUnitAddTorus,
      toAlgebraicTorusPoint, coords, coordUnit, coordsOfUnitAddTorus,
      unitAddTorusCoord]
  · apply Units.ext
    simp [ofUnitAddTorus, Flipped.AlgebraicTorusPoint.ofUnitAddTorus,
      toAlgebraicTorusPoint, coords, coordUnit, coordsOfUnitAddTorus,
      unitAddTorusCoord]
  · apply Units.ext
    simp [ofUnitAddTorus, Flipped.AlgebraicTorusPoint.ofUnitAddTorus,
      toAlgebraicTorusPoint, coords, coordUnit, coordsOfUnitAddTorus,
      unitAddTorusCoord]

end

end FlippedDiagonalSU6Point
end FlippedTorus

namespace NormalizedVirtualRestriction

open VirtualRestriction

noncomputable section

abbrev DiagonalSU6Point := FlippedTorus.FlippedDiagonalSU6Point
abbrev ActualSU6Representation := VirtualRestriction.ActualSU6Representation
abbrev FiniteVirtualSU6Representation :=
  VirtualRestriction.FiniteVirtualSU6Representation
abbrev Poly := Flipped.Normalized.Poly

def diagonalLaurentEval (p : Poly) (t : DiagonalSU6Point) : ℂ :=
  Flipped.Normalized.eval p t.toAlgebraicTorusPoint

abbrev DiagonalLaurentFaithful : Prop :=
  ∀ p q : Poly,
    (∀ t : DiagonalSU6Point,
      diagonalLaurentEval p t = diagonalLaurentEval q t) -> p = q

theorem diagonalLaurentFaithful : DiagonalLaurentFaithful := by
  intro p q h
  apply Flipped.Normalized.evalUnitAddTorus_faithful
  intro x
  have hx := h (FlippedTorus.FlippedDiagonalSU6Point.ofUnitAddTorus x)
  simpa [diagonalLaurentEval,
    FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint_ofUnitAddTorus,
    Flipped.Normalized.eval_ofUnitAddTorus] using hx

structure CommonLaurentEvaluator where
  eval : Poly -> DiagonalSU6Point -> ℂ
  eval_zero : ∀ t, eval 0 t = 0
  eval_add : ∀ p q t, eval (p + q) t = eval p t + eval q t
  eval_zscale :
    ∀ n p t, eval (Flipped.Normalized.zscale n p) t =
      (n : ℂ) * eval p t
  eval_swap36 :
    ∀ p t, eval (Flipped.Normalized.swap36 p) t =
      eval p (FlippedTorus.FlippedDiagonalSU6Point.swap36 t)
  faithful :
    ∀ p q, (∀ t, eval p t = eval q t) -> p = q

def commonLaurentEvaluatorOfFaithful
    (hfaithful : DiagonalLaurentFaithful) :
    CommonLaurentEvaluator where
  eval := diagonalLaurentEval
  eval_zero := by
    intro t
    exact Flipped.Normalized.eval_zero t.toAlgebraicTorusPoint
  eval_add := by
    intro p q t
    exact Flipped.Normalized.eval_add p q t.toAlgebraicTorusPoint
  eval_zscale := by
    intro n p t
    exact Flipped.Normalized.eval_zscale n p t.toAlgebraicTorusPoint
  eval_swap36 := by
    intro p t
    unfold diagonalLaurentEval
    rw [Flipped.Normalized.eval_swap36,
      ← FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint_swap36 t]
  faithful := hfaithful

def commonLaurentEvaluator : CommonLaurentEvaluator :=
  commonLaurentEvaluatorOfFaithful diagonalLaurentFaithful

structure ActualLaurentModelProvider (E : CommonLaurentEvaluator) where
  poly : ActualSU6Representation -> Poly
  evaluates_rep :
    ∀ R t, E.eval (poly R) t = R.restrictedCharacter t

namespace FiniteVirtualSU6Representation

def polyOfProvider {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E) :
    FiniteVirtualSU6Representation -> Poly
  | [] => 0
  | s :: ss =>
      Flipped.Normalized.zscale s.coeff (P.poly s.rep) + polyOfProvider P ss

theorem polyOfProvider_evaluates
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) (t : DiagonalSU6Point) :
    E.eval (polyOfProvider P χ) t =
      VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter χ t := by
  induction χ with
  | nil =>
      simp [polyOfProvider,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter,
        E.eval_zero]
  | cons s ss ih =>
      rw [polyOfProvider,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter,
        E.eval_add, E.eval_zscale, P.evaluates_rep, ih]
      rfl

theorem polyOfProvider_swap36_fixed
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    Flipped.Normalized.swap36 (polyOfProvider P χ) =
      polyOfProvider P χ := by
  apply E.faithful
  intro t
  rw [E.eval_swap36, polyOfProvider_evaluates P, polyOfProvider_evaluates P,
    VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed]

theorem polyOfProvider_ne_flippedSMCharacter
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E)
    (χ : FiniteVirtualSU6Representation) :
    polyOfProvider P χ ≠ Flipped.Normalized.flippedSMCharacter := by
  intro h
  have hfixed := polyOfProvider_swap36_fixed P χ
  rw [h] at hfixed
  exact Flipped.Normalized.swap36_flippedSMCharacter_ne hfixed

/--
A non-`swap36`-fixed normalized Laurent function cannot be the restricted
character of any finite virtual `SU(6)` representation.
-/
theorem no_restrictedCharacter_eq_diagonalLaurentEval_of_not_swap36_fixed
    (p : Poly)
    (hp : Flipped.Normalized.swap36 p ≠ p) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : DiagonalSU6Point,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            χ t =
          diagonalLaurentEval p t := by
  have hfaithful : Function.Injective diagonalLaurentEval :=
    fun _ _ h => diagonalLaurentFaithful _ _ (congrFun h)
  have hcompatible : ∀ q t,
      diagonalLaurentEval (Flipped.Normalized.swap36 q) t =
        diagonalLaurentEval q (FlippedTorus.FlippedDiagonalSU6Point.swap36 t) := by
    intro q t
    unfold diagonalLaurentEval
    rw [Flipped.Normalized.eval_swap36,
      ← FlippedTorus.FlippedDiagonalSU6Point.toAlgebraicTorusPoint_swap36 t]
  have hnot := CharacterRestriction.not_mem_range_of_nonfixed_model
    diagonalLaurentEval hfaithful Flipped.Normalized.swap36
    FlippedTorus.FlippedDiagonalSU6Point.swap36 hcompatible
    VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
    VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter_swap36_fixed p hp
  rintro ⟨χ, hχ⟩
  exact hnot ⟨χ, funext hχ⟩

/--
No finite virtual `SU(6)` restricted character can agree, as a function on the
actual flipped diagonal torus, with the normalized flipped-SM target.

This version does not assume that the arbitrary virtual character has first
been represented by a Laurent polynomial.  It uses only the kernel-checked
`(3 6)` Weyl invariance of finite virtual restricted characters and the
faithfulness of the normalized Laurent evaluator on the same actual subtorus.
-/
theorem no_restrictedCharacter_eq_flippedSMCharacter_eval :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : DiagonalSU6Point,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            χ t =
          diagonalLaurentEval Flipped.Normalized.flippedSMCharacter t :=
  no_restrictedCharacter_eq_diagonalLaurentEval_of_not_swap36_fixed
    Flipped.Normalized.flippedSMCharacter
    Flipped.Normalized.swap36_flippedSMCharacter_ne

/--
The same function-level obstruction holds for every nonzero integer multiple
of the flipped-SM target, in particular for any positive number of generations.
-/
theorem no_restrictedCharacter_eq_nonzero_generation_flippedSMCharacter_eval
    (n : ℤ) (hn : n ≠ 0) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : DiagonalSU6Point,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            χ t =
          diagonalLaurentEval
            (Flipped.Normalized.zscale n
              Flipped.Normalized.flippedSMCharacter) t :=
  no_restrictedCharacter_eq_diagonalLaurentEval_of_not_swap36_fixed
    (Flipped.Normalized.zscale n Flipped.Normalized.flippedSMCharacter)
    (Flipped.Normalized.swap36_zscale_flippedSMCharacter_ne n hn)

/--
Adding any `swap36`-fixed virtual sector cannot remove the nonzero-generation
obstruction.
-/
theorem no_restrictedCharacter_eq_nonzero_generation_add_fixed_eval
    (n : ℤ) (hn : n ≠ 0) (q : Poly)
    (hq : Flipped.Normalized.swap36 q = q) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : DiagonalSU6Point,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            χ t =
          diagonalLaurentEval
            (Flipped.Normalized.zscale n
                Flipped.Normalized.flippedSMCharacter + q) t :=
  no_restrictedCharacter_eq_diagonalLaurentEval_of_not_swap36_fixed
    (Flipped.Normalized.zscale n Flipped.Normalized.flippedSMCharacter + q)
    (Flipped.Normalized.swap36_add_fixed_ne
      (Flipped.Normalized.swap36_zscale_flippedSMCharacter_ne n hn) hq)

/--
In particular, no nonzero number of flipped-SM generations, with any integer
virtual multiplicity of gauge singlets, is such a restricted character.
-/
theorem no_restrictedCharacter_eq_nonzero_generation_add_singlets_eval
    (n : ℤ) (hn : n ≠ 0) (singlets : ℤ) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : DiagonalSU6Point,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            χ t =
          diagonalLaurentEval
            (Flipped.Normalized.zscale n
                Flipped.Normalized.flippedSMCharacter +
              Flipped.Normalized.singletCharacter singlets) t :=
  no_restrictedCharacter_eq_nonzero_generation_add_fixed_eval n hn
    (Flipped.Normalized.singletCharacter singlets)
    (Flipped.Normalized.swap36_singletCharacter singlets)

/-- Symmetric orientation of `no_restrictedCharacter_eq_flippedSMCharacter_eval`. -/
theorem no_flippedSMCharacter_eval_eq_restrictedCharacter :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      ∀ t : DiagonalSU6Point,
        diagonalLaurentEval Flipped.Normalized.flippedSMCharacter t =
          VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            χ t := by
  intro h
  rcases h with ⟨χ, hχ⟩
  exact no_restrictedCharacter_eq_flippedSMCharacter_eval
    ⟨χ, fun t => (hχ t).symm⟩

/-- The function-level restriction image of finite virtual `SU(6)` characters. -/
def finiteVirtualRestrictedCharacterImage :
    Set (DiagonalSU6Point → ℂ) :=
  Set.range fun χ : FiniteVirtualSU6Representation =>
    VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter χ

/-- The normalized flipped-SM target viewed as a function on the actual torus. -/
def flippedSMCharacterEval : DiagonalSU6Point → ℂ :=
  fun t => diagonalLaurentEval Flipped.Normalized.flippedSMCharacter t

/--
Function-ring form of the flipped-branch obstruction: the target is outside
the restriction image of all finite virtual `SU(6)` characters.
-/
theorem flippedSMCharacterEval_not_mem_finiteVirtualRestrictedCharacterImage :
    flippedSMCharacterEval ∉ finiteVirtualRestrictedCharacterImage := by
  intro h
  rcases h with ⟨χ, hχ⟩
  apply no_restrictedCharacter_eq_flippedSMCharacter_eval
  exact ⟨χ, fun t => congrFun hχ t⟩

theorem no_flippedSM_uplift_of_actual_provider
    {E : CommonLaurentEvaluator}
    (P : ActualLaurentModelProvider E) :
    ¬ ∃ χ : FiniteVirtualSU6Representation,
      polyOfProvider P χ = Flipped.Normalized.flippedSMCharacter := by
  intro h
  rcases h with ⟨χ, hχ⟩
  exact polyOfProvider_ne_flippedSMCharacter P χ hχ

end FiniteVirtualSU6Representation

structure ActualTorusWeightCharacter
    (R : ActualSU6Representation) where
  poly : Poly
  evaluates_restrictedCharacter :
    ∀ t : DiagonalSU6Point,
      diagonalLaurentEval poly t = R.restrictedCharacter t

end

end NormalizedVirtualRestriction

namespace WeightTheory

noncomputable section

/-!
`PhysicallyAdmissibleSU6Representation` is the current formal cut for the
representations that should be covered by the Laurent bridge: an actual
finite-dimensional SU(6) representation together with its torus weight
eigenbasis.  This deliberately avoids asserting Laurent polynomiality for an
arbitrary abstract group representation.
-/
structure PhysicallyAdmissibleSU6Representation where
  toActual : ActualSU6Representation
  eigenbasis : TorusEigenbasis toActual

namespace TorusEigenbasis

def toActualNormalizedTorusWeightCharacter
    {R : ActualSU6Representation}
    (D : TorusEigenbasis R) :
    NormalizedVirtualRestriction.ActualTorusWeightCharacter R where
  poly := Flipped.Normalized.ofRawCharacter D.rawCharacter
  evaluates_restrictedCharacter := by
    intro t
    rw [NormalizedVirtualRestriction.diagonalLaurentEval,
      Flipped.Normalized.eval_ofRawCharacter, rawCharacter,
      rawCharacterOfWeights_eval]
    exact (D.restrictedCharacter_eq_sum t).symm

end TorusEigenbasis

namespace PhysicallyAdmissibleSU6Representation

def normalizedCharacter (R : PhysicallyAdmissibleSU6Representation) :
    NormalizedVirtualRestriction.ActualTorusWeightCharacter R.toActual :=
  R.eigenbasis.toActualNormalizedTorusWeightCharacter

end PhysicallyAdmissibleSU6Representation

def actualNormalizedLaurentModelProviderOfEigenbasisTheory
    (hfaithful : NormalizedVirtualRestriction.DiagonalLaurentFaithful)
    (T : SU6TorusEigenbasisTheory) :
    NormalizedVirtualRestriction.ActualLaurentModelProvider
      (NormalizedVirtualRestriction.commonLaurentEvaluatorOfFaithful hfaithful) where
  poly := fun R =>
    ((T.eigenbasis R).toActualNormalizedTorusWeightCharacter).poly
  evaluates_rep := by
    intro R t
    exact
      ((T.eigenbasis R).toActualNormalizedTorusWeightCharacter).evaluates_restrictedCharacter t

theorem finiteVirtual_normalized_poly_swap36_fixed_of_eigenbasisTheory
    (hfaithful : NormalizedVirtualRestriction.DiagonalLaurentFaithful)
    (T : SU6TorusEigenbasisTheory)
    (χ : VirtualRestriction.FiniteVirtualSU6Representation) :
    Flipped.Normalized.swap36
        (NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
          (actualNormalizedLaurentModelProviderOfEigenbasisTheory hfaithful T) χ) =
      NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
        (actualNormalizedLaurentModelProviderOfEigenbasisTheory hfaithful T) χ := by
  exact
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider_swap36_fixed
      (actualNormalizedLaurentModelProviderOfEigenbasisTheory hfaithful T) χ

theorem no_flippedSM_normalized_uplift_of_eigenbasisTheory
    (hfaithful : NormalizedVirtualRestriction.DiagonalLaurentFaithful)
    (T : SU6TorusEigenbasisTheory) :
    ¬ ∃ χ : VirtualRestriction.FiniteVirtualSU6Representation,
      NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
        (actualNormalizedLaurentModelProviderOfEigenbasisTheory hfaithful T) χ =
          Flipped.Normalized.flippedSMCharacter := by
  exact
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider
      (actualNormalizedLaurentModelProviderOfEigenbasisTheory hfaithful T)

def actualNormalizedLaurentModelProvider
    (T : SU6TorusEigenbasisTheory) :
    NormalizedVirtualRestriction.ActualLaurentModelProvider
      NormalizedVirtualRestriction.commonLaurentEvaluator :=
  actualNormalizedLaurentModelProviderOfEigenbasisTheory
    NormalizedVirtualRestriction.diagonalLaurentFaithful T

theorem finiteVirtual_normalized_poly_swap36_fixed
    (T : SU6TorusEigenbasisTheory)
    (χ : VirtualRestriction.FiniteVirtualSU6Representation) :
    Flipped.Normalized.swap36
        (NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
          (actualNormalizedLaurentModelProvider T) χ) =
      NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
        (actualNormalizedLaurentModelProvider T) χ := by
  exact
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider_swap36_fixed
      (actualNormalizedLaurentModelProvider T) χ

theorem no_flippedSM_normalized_uplift
    (T : SU6TorusEigenbasisTheory) :
    ¬ ∃ χ : VirtualRestriction.FiniteVirtualSU6Representation,
      NormalizedVirtualRestriction.FiniteVirtualSU6Representation.polyOfProvider
        (actualNormalizedLaurentModelProvider T) χ =
          Flipped.Normalized.flippedSMCharacter := by
  exact
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_flippedSM_uplift_of_actual_provider
      (actualNormalizedLaurentModelProvider T)

end

end WeightTheory
end GUT
