import GUT.SU6.SelectionRules.FlippedBranch.Flipped
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-!
# Evaluation of the flipped Laurent-polynomial syntax

This file gives the syntactic Laurent model in `GUT.Flipped` an explicit
evaluation on the algebraic flipped torus `(ℂˣ)^4`.

The main checked point is `Poly.eval_swap36`: the concrete evaluation of
`Flipped.swap36 p` at a torus point is the same as evaluating `p` at the
swapped torus point.  This makes the "swap-compatible Laurent evaluator"
condition computational for the algebraic torus model.  Faithfulness of
evaluation on the relevant function space is still kept separate from this
file.
-/

namespace GUT
namespace Flipped

noncomputable section

structure AlgebraicTorusPoint where
  z1 : ℂˣ
  z2 : ℂˣ
  z3 : ℂˣ
  z4 : ℂˣ

@[ext]
theorem AlgebraicTorusPoint.ext
    {p q : AlgebraicTorusPoint}
    (h1 : p.z1 = q.z1)
    (h2 : p.z2 = q.z2)
    (h3 : p.z3 = q.z3)
    (h4 : p.z4 = q.z4) :
    p = q := by
  cases p
  cases q
  simp_all

namespace AlgebraicTorusPoint

def z5 (p : AlgebraicTorusPoint) : ℂˣ :=
  p.z4⁻¹

def z6 (p : AlgebraicTorusPoint) : ℂˣ :=
  (p.z1 * p.z2 * p.z3)⁻¹

def swap36 (p : AlgebraicTorusPoint) : AlgebraicTorusPoint where
  z1 := p.z1
  z2 := p.z2
  z3 := p.z6
  z4 := p.z4

theorem swap36_involutive (p : AlgebraicTorusPoint) :
    swap36 (swap36 p) = p := by
  ext <;> simp [swap36, z6]
  field_simp [Units.ne_zero p.z1, Units.ne_zero p.z2]

end AlgebraicTorusPoint

namespace Exp

theorem eq_of_cmpInt_eq {a b : Int}
    (h : cmpInt a b = Ordering.eq) : a = b := by
  unfold cmpInt at h
  by_cases hlt : a < b
  · simp [hlt] at h
  · by_cases heq : a = b
    · exact heq
    · simp [hlt, heq] at h

theorem eq_of_cmp_eq {a b : Exp}
    (h : cmp a b = Ordering.eq) : a = b := by
  cases a with | mk a1 a2 a3 a4 =>
  cases b with | mk b1 b2 b3 b4 =>
  unfold cmp at h
  cases h1 : cmpInt a1 b1 with
  | lt => simp [h1] at h
  | eq =>
      have hz1 : a1 = b1 := eq_of_cmpInt_eq h1
      cases h2 : cmpInt a2 b2 with
      | lt => simp [h1, h2] at h
      | eq =>
          have hz2 : a2 = b2 := eq_of_cmpInt_eq h2
          cases h3 : cmpInt a3 b3 with
          | lt => simp [h1, h2, h3] at h
          | eq =>
              have hz3 : a3 = b3 := eq_of_cmpInt_eq h3
              have h4 : cmpInt a4 b4 = Ordering.eq := by
                simpa [h1, h2, h3] using h
              have hz4 : a4 = b4 := eq_of_cmpInt_eq h4
              subst b1
              subst b2
              subst b3
              subst b4
              rfl
          | gt => simp [h1, h2, h3] at h
      | gt => simp [h1, h2] at h
  | gt => simp [h1] at h

def evalUnit (e : Exp) (p : AlgebraicTorusPoint) : ℂˣ :=
  p.z1 ^ e.z1 * p.z2 ^ e.z2 * p.z3 ^ e.z3 * p.z4 ^ e.z4

def eval (e : Exp) (p : AlgebraicTorusPoint) : ℂ :=
  evalUnit e p

theorem eval_add_mul (e f : Exp) (x : AlgebraicTorusPoint) :
    (Exp.add e f).eval x = e.eval x * f.eval x := by
  cases e
  cases f
  simp [Exp.add, Exp.eval, Exp.evalUnit, zpow_add]
  ring

theorem evalUnit_swap36Exp (e : Exp) (p : AlgebraicTorusPoint) :
    evalUnit (swap36Exp e) p = evalUnit e (AlgebraicTorusPoint.swap36 p) := by
  cases e with | mk a b c d =>
  change
    p.z1 ^ (a - c) * p.z2 ^ (b - c) * p.z3 ^ (-c) * p.z4 ^ d =
      p.z1 ^ a * p.z2 ^ b * ((p.z1 * p.z2 * p.z3)⁻¹) ^ c * p.z4 ^ d
  rw [zpow_sub p.z1 a c, zpow_sub p.z2 b c]
  rw [inv_zpow' (p.z1 * p.z2 * p.z3) c]
  rw [mul_zpow, mul_zpow]
  rw [zpow_neg p.z1 c, zpow_neg p.z2 c]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem eval_swap36Exp (e : Exp) (p : AlgebraicTorusPoint) :
    eval (swap36Exp e) p = eval e (AlgebraicTorusPoint.swap36 p) := by
  exact congrArg Units.val (evalUnit_swap36Exp e p)

end Exp

namespace Term

def eval (t : Term) (p : AlgebraicTorusPoint) : ℂ :=
  (t.coeff : ℂ) * t.exp.eval p

end Term

namespace Poly

def evalTerms : List Term -> AlgebraicTorusPoint -> ℂ
  | [], _ => 0
  | t :: ts, p => t.eval p + evalTerms ts p

def eval (p : Poly) (x : AlgebraicTorusPoint) : ℂ :=
  evalTerms p.terms x

theorem evalTerms_insertTerm
    (e : Exp) (c : Int) (ts : List Term) (x : AlgebraicTorusPoint) :
    evalTerms (insertTerm e c ts) x =
      (c : ℂ) * e.eval x + evalTerms ts x := by
  induction ts with
  | nil =>
      by_cases hc : c = 0
      · simp [insertTerm, evalTerms, hc]
      · simp [insertTerm, evalTerms, Term.eval, hc]
  | cons t ts ih =>
      unfold insertTerm
      cases hcmp : Exp.cmp e t.exp
      · by_cases hc : c = 0
        · simp [evalTerms, Term.eval, hc]
        · simp [evalTerms, Term.eval, hc]
      · have he : e = t.exp := Exp.eq_of_cmp_eq hcmp
        subst e
        by_cases hzero : c + t.coeff = 0
        · simp [hzero, evalTerms, Term.eval]
          have hcast : (c : ℂ) + (t.coeff : ℂ) = 0 := by
            exact_mod_cast hzero
          calc
            evalTerms ts x
                = ((c : ℂ) + (t.coeff : ℂ)) * t.exp.eval x + evalTerms ts x := by
                    simp [hcast]
            _ = (c : ℂ) * t.exp.eval x +
                  ((t.coeff : ℂ) * t.exp.eval x + evalTerms ts x) := by
                    ring
        · simp [hzero, evalTerms, Term.eval]
          ring
      · simp [evalTerms, Term.eval, ih]
        ring_nf

theorem evalTerms_foldl_insertTerm
    (newTerms acc : List Term) (x : AlgebraicTorusPoint) :
    evalTerms
        (newTerms.foldl
          (fun acc t => insertTerm t.exp t.coeff acc)
          acc)
        x =
      evalTerms acc x + evalTerms newTerms x := by
  induction newTerms generalizing acc with
  | nil =>
      simp [evalTerms]
  | cons t ts ih =>
      simp [evalTerms, Term.eval]
      rw [ih, evalTerms_insertTerm]
      ring_nf

theorem eval_zero (x : AlgebraicTorusPoint) :
    eval 0 x = 0 := by
  rfl

theorem eval_add (p q : Poly) (x : AlgebraicTorusPoint) :
    eval (p + q) x = eval p x + eval q x := by
  change eval (add p q) x = eval p x + eval q x
  simp [eval, add, evalTerms_foldl_insertTerm]

theorem evalTerms_zscale
    (n : Int) (terms : List Term) (x : AlgebraicTorusPoint) :
    evalTerms
        (terms.map (fun t => { exp := t.exp, coeff := n * t.coeff }))
        x =
      (n : ℂ) * evalTerms terms x := by
  induction terms with
  | nil =>
      simp [evalTerms]
  | cons t ts ih =>
      simp [evalTerms, Term.eval, ih]
      ring

theorem eval_zscale (n : Int) (p : Poly) (x : AlgebraicTorusPoint) :
    eval (zscale n p) x = (n : ℂ) * eval p x := by
  simp [eval, zscale, evalTerms_zscale]

theorem eval_neg (p : Poly) (x : AlgebraicTorusPoint) :
    eval (-p) x = -eval p x := by
  change
    evalTerms
        (p.terms.map (fun t => { exp := t.exp, coeff := -t.coeff })) x =
      -evalTerms p.terms x
  simpa using evalTerms_zscale (-1) p.terms x

theorem eval_sub (p q : Poly) (x : AlgebraicTorusPoint) :
    eval (p - q) x = eval p x - eval q x := by
  change eval (add p (neg q)) x = _
  calc
    eval (add p (neg q)) x = eval p x + eval (neg q) x :=
      eval_add p (neg q) x
    _ = eval p x + (-eval q x) := by
      congr 1
      change eval (-q) x = -eval q x
      exact eval_neg q x
    _ = eval p x - eval q x := by ring

theorem evalTerms_foldl_mul_inner
    (t : Term) (terms acc : List Term) (x : AlgebraicTorusPoint) :
    evalTerms
        (terms.foldl
          (fun acc u =>
            insertTerm (Exp.add t.exp u.exp) (t.coeff * u.coeff) acc)
          acc) x =
      evalTerms acc x + t.eval x * evalTerms terms x := by
  induction terms generalizing acc with
  | nil => simp [evalTerms]
  | cons u us ih =>
      rw [List.foldl_cons, ih, evalTerms_insertTerm]
      simp [evalTerms, Term.eval, Exp.eval_add_mul]
      ring

theorem evalTerms_foldl_mul_outer
    (left right acc : List Term) (x : AlgebraicTorusPoint) :
    evalTerms
        (left.foldl
          (fun acc t =>
            right.foldl
              (fun acc u =>
                insertTerm (Exp.add t.exp u.exp) (t.coeff * u.coeff) acc)
              acc)
          acc) x =
      evalTerms acc x + evalTerms left x * evalTerms right x := by
  induction left generalizing acc with
  | nil => simp [evalTerms]
  | cons t ts ih =>
      rw [List.foldl_cons, ih, evalTerms_foldl_mul_inner]
      simp [evalTerms]
      ring

theorem eval_mul (p q : Poly) (x : AlgebraicTorusPoint) :
    eval (p * q) x = eval p x * eval q x := by
  change
    evalTerms
        (p.terms.foldl
          (fun acc t =>
            q.terms.foldl
              (fun acc u =>
                insertTerm (Exp.add t.exp u.exp) (t.coeff * u.coeff) acc)
              acc)
          []) x = _
  rw [evalTerms_foldl_mul_outer]
  simp [eval, evalTerms]

theorem eval_mon (a b c d coeff : ℤ) (x : AlgebraicTorusPoint) :
    eval (mon a b c d coeff) x =
      (coeff : ℂ) *
        ((x.z1 : ℂ) ^ a * (x.z2 : ℂ) ^ b *
          (x.z3 : ℂ) ^ c * (x.z4 : ℂ) ^ d) := by
  simp [mon, eval, ofTerm, evalTerms_insertTerm, evalTerms,
    Exp.eval, Exp.evalUnit]

theorem evalTerms_foldl_mapExp
    (f : Exp -> Exp) (newTerms acc : List Term)
    (x y : AlgebraicTorusPoint)
    (hf : ∀ e, Exp.eval (f e) x = Exp.eval e y) :
    evalTerms
        (newTerms.foldl
          (fun acc t => insertTerm (f t.exp) t.coeff acc)
          acc)
        x =
      evalTerms acc x + evalTerms newTerms y := by
  induction newTerms generalizing acc with
  | nil =>
      simp [evalTerms]
  | cons t ts ih =>
      simp [evalTerms, Term.eval]
      rw [ih, evalTerms_insertTerm]
      simp [hf]
      ring_nf

theorem eval_mapExp
    (f : Exp -> Exp) (p : Poly) (x y : AlgebraicTorusPoint)
    (hf : ∀ e, Exp.eval (f e) x = Exp.eval e y) :
    eval (mapExp f p) x = eval p y := by
  rw [eval, mapExp]
  change
    evalTerms
        (p.terms.foldl
          (fun acc t => insertTerm (f t.exp) t.coeff acc)
          [])
        x =
      evalTerms p.terms y
  rw [evalTerms_foldl_mapExp f p.terms [] x y hf]
  simp [evalTerms]

theorem eval_swap36 (p : Poly) (x : AlgebraicTorusPoint) :
    eval (Flipped.swap36 p) x =
      eval p (AlgebraicTorusPoint.swap36 x) := by
  exact eval_mapExp swap36Exp p x (AlgebraicTorusPoint.swap36 x)
    (fun e => Exp.eval_swap36Exp e x)

end Poly

namespace RawCharacter

def eval : RawCharacter Exp -> AlgebraicTorusPoint -> ℂ
  | [], _ => 0
  | m :: ms, x => (m.coeff : ℂ) * m.exp.eval x + eval ms x

theorem evalTerms_foldl_insertMonomial
    (χ : RawCharacter Exp) (acc : List Term) (x : AlgebraicTorusPoint) :
    Poly.evalTerms
        (χ.foldl
          (fun acc m => Poly.insertTerm m.exp m.coeff acc)
          acc)
        x =
      Poly.evalTerms acc x + eval χ x := by
  induction χ generalizing acc with
  | nil =>
      simp [eval]
  | cons m ms ih =>
      cases m
      simp [eval]
      rw [ih, Poly.evalTerms_insertTerm]
      ring_nf

theorem eval_toPoly (χ : RawCharacter Exp) (x : AlgebraicTorusPoint) :
    Poly.eval (toPoly χ) x = eval χ x := by
  rw [Poly.eval, toPoly]
  rw [evalTerms_foldl_insertMonomial χ [] x]
  simp [Poly.evalTerms]

theorem eval_mapWeights_one
    {ι : Type*} (weight : ι -> Exp) (is : List ι)
    (x : AlgebraicTorusPoint) :
    eval (is.map (fun i => { exp := weight i, coeff := 1 })) x =
      (is.map (fun i => Exp.eval (weight i) x)).sum := by
  induction is with
  | nil =>
      simp [eval]
  | cons i is ih =>
      simp [eval, ih]

end RawCharacter

end

end Flipped
end GUT
