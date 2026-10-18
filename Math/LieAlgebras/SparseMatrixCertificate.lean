import Mathlib.Data.Matrix.Basis
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

/-!
# Sound sparse integer matrix certificates

Lists are certificate syntax only. Their meaning is an ordinary integer
matrix. Normalization need not be canonical: a successful zero check is
proved sound, and no external computation is part of the trust boundary.
-/

set_option autoImplicit false

namespace Math.SparseMatrixCertificate

variable {n : Type*} [DecidableEq n]

abbrev Entry (n : Type*) := (n × n) × ℤ
abbrev Code (n : Type*) := List (Entry n)

def atom (e : Entry n) : Matrix n n ℤ := Matrix.single e.1.1 e.1.2 e.2

def eval : Code n → Matrix n n ℤ
  | [] => 0
  | e :: es => atom e + eval es

@[simp] theorem eval_nil : eval ([] : Code n) = 0 := rfl
@[simp] theorem eval_cons (e : Entry n) (es : Code n) :
    eval (e :: es) = atom e + eval es := rfl

@[simp] theorem eval_append (a b : Code n) : eval (a ++ b) = eval a + eval b := by
  induction a with
  | nil => simp
  | cons e es ih => simp [ih, add_assoc]

def insert (e : Entry n) : Code n → Code n
  | [] => [e]
  | f :: fs => if e.1 = f.1 then (f.1, e.2 + f.2) :: fs else f :: insert e fs

theorem eval_insert (e : Entry n) (es : Code n) :
    eval (insert e es) = atom e + eval es := by
  induction es with
  | nil => simp [insert]
  | cons f fs ih =>
    by_cases h : e.1 = f.1
    · simp only [insert, h, ite_true, eval_cons]
      have he : atom (f.1, e.2 + f.2) = atom e + atom f := by
        simp [atom, h, Matrix.single_add]
      rw [he, add_assoc]
    · simp [insert, h, ih, add_left_comm]

def normalize : Code n → Code n
  | [] => []
  | e :: es => insert e (normalize es)

theorem eval_normalize (es : Code n) : eval (normalize es) = eval es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [normalize, eval_insert, ih]

def scale (z : ℤ) (es : Code n) : Code n := es.map fun e => (e.1, z * e.2)

theorem eval_scale (z : ℤ) (es : Code n) : eval (scale z es) = z • eval es := by
  induction es with
  | nil => simp [scale]
  | cons e es ih =>
    simp only [scale] at ih
    simp [scale, ih, atom, smul_add, Matrix.smul_single]

def checkZero (es : Code n) : Bool := (normalize es).all fun e => e.2 == 0

theorem checkZero_sound (es : Code n) (h : checkZero es = true) : eval es = 0 := by
  have hzero : ∀ e ∈ normalize es, e.2 = 0 := by simpa [checkZero] using h
  rw [← eval_normalize]
  generalize normalize es = zs at *
  induction zs with
  | nil => rfl
  | cons e es ih =>
    have he : e.2 = 0 := hzero e (by simp)
    simp [atom, he, ih (fun f hf => hzero f (by simp [hf]))]

def checkEq (a b : Code n) : Bool := checkZero (a ++ scale (-1) b)

theorem checkEq_sound (a b : Code n) (h : checkEq a b = true) : eval a = eval b := by
  have hz := checkZero_sound _ h
  apply sub_eq_zero.mp
  simpa only [eval_append, eval_scale, neg_one_zsmul, sub_eq_add_neg] using hz

def mulEntry (e f : Entry n) : Code n :=
  if e.1.2 = f.1.1 then [((e.1.1, f.1.2), e.2 * f.2)] else []

def mul (a b : Code n) : Code n := a.flatMap fun e => b.flatMap (mulEntry e)

variable [Fintype n]

theorem eval_mulEntry (e f : Entry n) : eval (mulEntry e f) = atom e * atom f := by
  by_cases h : e.1.2 = f.1.1
  · simp [mulEntry, h, atom, Matrix.single_mul_single_same]
  · simp [mulEntry, h, atom, Matrix.single_mul_single_of_ne _ _ _ _ h]

theorem eval_mul (a b : Code n) : eval (mul a b) = eval a * eval b := by
  have inner (e : Entry n) : eval (b.flatMap (mulEntry e)) = atom e * eval b := by
    induction b with
    | nil => simp
    | cons f fs ih => simp [eval_mulEntry, ih, mul_add]
  induction a with
  | nil => simp [mul]
  | cons e es ih =>
    simp only [mul] at ih
    simp [mul, inner, ih, add_mul]

def bracket (a b : Code n) : Code n := mul a b ++ scale (-1) (mul b a)

theorem eval_bracket (a b : Code n) :
    eval (bracket a b) = eval a * eval b - eval b * eval a := by
  simp [bracket, eval_mul, eval_scale, sub_eq_add_neg]

def combination {ι : Type*} (v : ι → Code n) (c : List (ι × ℤ)) : Code n :=
  c.flatMap fun p => scale p.2 (v p.1)

theorem eval_combination {ι : Type*} (v : ι → Code n) (c : List (ι × ℤ)) :
    eval (combination v c) = (c.map fun p => p.2 • eval (v p.1)).sum := by
  induction c with
  | nil => rfl
  | cons p ps ih =>
    simp only [combination] at ih
    simp [combination, eval_scale, ih]

def entryValue (a : Code n) (p : n × n) : ℤ :=
  (a.map fun e => if e.1 = p then e.2 else 0).sum

omit [Fintype n] in
theorem entryValue_eq (a : Code n) (p : n × n) : entryValue a p = eval a p.1 p.2 := by
  induction a with
  | nil => rfl
  | cons e es ih =>
    simp only [entryValue, Prod.ext_iff] at ih
    simp [entryValue, atom, Matrix.single_apply, Prod.ext_iff, ih]

def pairing (a b : Code n) : ℤ := (a.map fun e => e.2 * entryValue b e.1).sum

variable (R : Type*) [CommRing R]

/-- Interpretation over a scalar ring; the mathematical model is a matrix. -/
def realize (a : Code n) : Matrix n n R := (eval a).map (Int.castRingHom R)

omit [Fintype n] in
@[simp] theorem realize_apply (a : Code n) (i j : n) :
    realize R a i j = (eval a i j : R) := rfl

theorem realize_bracket (a b : Code n) :
    realize R (bracket a b) = realize R a * realize R b - realize R b * realize R a := by
  ext i j
  simp [realize, eval_bracket, Matrix.mul_apply, Int.cast_sum, Int.cast_mul, Int.cast_sub]

omit [Fintype n] in
theorem realize_combination_mem {ι : Type*} (v : ι → Code n) (c : List (ι × ℤ))
    (P : Submodule R (Matrix n n R)) (hv : ∀ i, realize R (v i) ∈ P) :
    realize R (combination v c) ∈ P := by
  induction c with
  | nil => simp [combination, realize]
  | cons p ps ih =>
    have he : realize R (combination v (p :: ps)) =
        (p.2 : R) • realize R (v p.1) + realize R (combination v ps) := by
      ext i j
      simp only [realize, combination, List.flatMap_cons, eval_append, eval_scale,
        Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_add,
        Int.cast_mul, Int.coe_castRingHom]
    rw [he]
    exact P.add_mem (P.smul_mem _ (hv p.1)) ih

/-- A coordinate functional used as a checked left-inverse witness. -/
def coordinate (p : n × n) : Matrix n n R →ₗ[R] R where
  toFun M := M p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def functional : Code n → Matrix n n R →ₗ[R] R
  | [] => 0
  | e :: es => (e.2 : R) • coordinate R e.1 + functional es

omit [Fintype n] in
theorem functional_realize (d a : Code n) :
    functional R d (realize R a) = (pairing d a : R) := by
  induction d with
  | nil => simp [functional, pairing]
  | cons e es ih =>
    change (e.2 : R) * realize R a e.1.1 e.1.2 + functional R es (realize R a) = _
    rw [ih]
    simp [pairing, entryValue_eq, Int.cast_add, Int.cast_mul]

end Math.SparseMatrixCertificate

namespace Math.SparseMatrixCertificate

variable {n ι K : Type*} [DecidableEq n] [Fintype n] [Fintype ι] [DecidableEq ι]
  [Field K] [CharZero K]

omit [Fintype n] in
theorem linearIndependent_of_pairing (v d : ι → Code n) (scale : ι → ℤ)
    (hnz : ∀ i, scale i ≠ 0)
    (hpair : ∀ i j, pairing (d i) (v j) = if i = j then scale i else 0) :
    LinearIndependent K (fun i => realize K (v i)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (functional K (d i)) hc
  simp only [map_sum, map_smul, map_zero, functional_realize] at h
  simp [hpair] at h
  exact h.resolve_right (hnz i)

end Math.SparseMatrixCertificate
