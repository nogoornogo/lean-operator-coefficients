import Math.LieAlgebras.SparseMatrixCertificate

/-!
# Checked sparse cubic certificates

Lists are certificate syntax, interpreted as ordinary cubic functions.
Sorting monomials and collecting coefficients gives a sound zero test.
Infinitesimal invariance is checked against actual sparse matrix actions.
-/

set_option autoImplicit false

namespace Math.SparseCubicCertificate

variable {n R : Type*} [CommRing R]

abbrev Triple (n : Type*) := n × n × n
abbrev Term (n : Type*) := Triple n × ℤ
abbrev Code (n : Type*) := List (Term n)

def value (e : Term n) (v : n → R) : R :=
  (e.2 : R) * v e.1.1 * v e.1.2.1 * v e.1.2.2

def eval : Code n → (n → R) → R
  | [], _ => 0
  | e :: es, v => value e v + eval es v

def differential : Code n → (n → R) → (n → R) → R
  | [], _, _ => 0
  | e :: es, v, w => (e.2 : R) *
      (w e.1.1 * v e.1.2.1 * v e.1.2.2 +
       v e.1.1 * w e.1.2.1 * v e.1.2.2 +
       v e.1.1 * v e.1.2.1 * w e.1.2.2) + differential es v w

theorem eval_append (a b : Code n) (v : n → R) : eval (a ++ b) v = eval a v + eval b v := by
  induction a with
  | nil => simp [eval]
  | cons e es ih => simp [eval, ih, add_assoc]

theorem eval_smul (p : Code n) (z : R) (v : n → R) :
    eval p (z • v) = z ^ 3 * eval p v := by
  induction p with
  | nil => simp [eval]
  | cons e es ih => simp only [eval, value, Pi.smul_apply, smul_eq_mul, ih]; ring

theorem differential_zero (p : Code n) (v : n → R) : differential p v 0 = 0 := by
  induction p with
  | nil => rfl
  | cons e es ih => simp [differential, ih]

theorem differential_add (p : Code n) (v w u : n → R) :
    differential p v (w + u) = differential p v w + differential p v u := by
  induction p with
  | nil => simp [differential]
  | cons e es ih => simp only [differential, Pi.add_apply, ih]; ring

theorem differential_smul (p : Code n) (v w : n → R) (z : R) :
    differential p v (z • w) = z * differential p v w := by
  induction p with
  | nil => simp [differential]
  | cons e es ih => simp only [differential, Pi.smul_apply, smul_eq_mul, ih]; ring

variable [LinearOrder n]

def sortTriple (t : Triple n) : Triple n :=
  if t.1 ≤ t.2.1 then
    if t.2.1 ≤ t.2.2 then t
    else if t.1 ≤ t.2.2 then (t.1, t.2.2, t.2.1) else (t.2.2, t.1, t.2.1)
  else if t.1 ≤ t.2.2 then (t.2.1, t.1, t.2.2)
    else if t.2.1 ≤ t.2.2 then (t.2.1, t.2.2, t.1) else (t.2.2, t.2.1, t.1)

theorem value_sort (e : Term n) (v : n → R) : value (sortTriple e.1, e.2) v = value e v := by
  unfold sortTriple
  split_ifs <;> simp only [value] <;> ring

def insert (e : Term n) : Code n → Code n
  | [] => [e]
  | f :: fs => if e.1 = f.1 then (f.1, e.2 + f.2) :: fs else f :: insert e fs

theorem eval_insert (e : Term n) (p : Code n) (v : n → R) :
    eval (insert e p) v = value e v + eval p v := by
  induction p with
  | nil => simp [insert, eval]
  | cons f fs ih =>
    by_cases h : e.1 = f.1
    · simp [insert, h, eval, value, Int.cast_add]; ring
    · simp [insert, h, eval, ih, add_left_comm]

def normalize : Code n → Code n
  | [] => []
  | e :: es => insert (sortTriple e.1, e.2) (normalize es)

theorem eval_normalize (p : Code n) (v : n → R) : eval (normalize p) v = eval p v := by
  induction p with
  | nil => rfl
  | cons e es ih => simp [normalize, eval_insert, value_sort, eval, ih]

def checkZero (p : Code n) : Bool := (normalize p).all fun e => e.2 == 0

theorem checkZero_sound (p : Code n) (hp : checkZero p = true) (v : n → R) : eval p v = 0 := by
  have hz : ∀ e ∈ normalize p, e.2 = 0 := by simpa [checkZero] using hp
  rw [← eval_normalize]
  generalize normalize p = q at *
  induction q with
  | nil => rfl
  | cons e es ih =>
    have he := hz e (by simp)
    simp [eval, value, he, ih (fun f hf => hz f (by simp [hf]))]

def actTerm (m : SparseMatrixCertificate.Entry n) (e : Term n) : Code n :=
  (if e.1.1 = m.1.1 then [((m.1.2, e.1.2.1, e.1.2.2), e.2 * m.2)] else []) ++
  (if e.1.2.1 = m.1.1 then [((e.1.1, m.1.2, e.1.2.2), e.2 * m.2)] else []) ++
  (if e.1.2.2 = m.1.1 then [((e.1.1, e.1.2.1, m.1.2), e.2 * m.2)] else [])

def actEntry (m : SparseMatrixCertificate.Entry n) (p : Code n) : Code n :=
  p.flatMap (actTerm m)

def act (M : SparseMatrixCertificate.Code n) (p : Code n) : Code n :=
  M.flatMap fun m => actEntry m p

variable [Fintype n]
open scoped Matrix

theorem eval_actTerm (m : SparseMatrixCertificate.Entry n) (e : Term n) (v : n → R) :
    eval (actTerm m e) v = differential [e] v
      (Matrix.single m.1.1 m.1.2 (m.2 : R) *ᵥ v) := by
  simp only [actTerm, eval_append, Matrix.single_mulVec, differential]
  split_ifs <;> simp_all [eval, value, Int.cast_mul] <;> ring

theorem eval_actEntry (m : SparseMatrixCertificate.Entry n) (p : Code n) (v : n → R) :
    eval (actEntry m p) v = differential p v
      (Matrix.single m.1.1 m.1.2 (m.2 : R) *ᵥ v) := by
  induction p with
  | nil => rfl
  | cons e es ih =>
    simp only [actEntry, List.flatMap_cons, eval_append] at *
    rw [eval_actTerm, ih]
    simp [differential, add_assoc]

theorem eval_act (M : SparseMatrixCertificate.Code n) (p : Code n) (v : n → R) :
    eval (act M p) v = differential p v (SparseMatrixCertificate.realize R M *ᵥ v) := by
  induction M with
  | nil => simp [act, eval, SparseMatrixCertificate.realize, SparseMatrixCertificate.eval,
      differential_zero]
  | cons m ms ih =>
    have hm : SparseMatrixCertificate.realize R (m :: ms) =
        Matrix.single m.1.1 m.1.2 (m.2 : R) + SparseMatrixCertificate.realize R ms := by
      ext i j
      simp [SparseMatrixCertificate.realize, SparseMatrixCertificate.eval,
        SparseMatrixCertificate.atom, Matrix.single_apply]
    simp only [act, List.flatMap_cons, eval_append] at *
    rw [eval_actEntry, ih, hm, Matrix.add_mulVec, differential_add]

/-- The kernel of the infinitesimal action on a fixed cubic, as a linear subspace. -/
def annihilator (p : Code n) : Submodule R (Matrix n n R) where
  carrier := {M | ∀ v, differential p v (M *ᵥ v) = 0}
  zero_mem' := by intro v; simp [differential_zero]
  add_mem' := by
    intro A B hA hB v
    rw [Matrix.add_mulVec, differential_add, hA, hB, add_zero]
  smul_mem' := by
    intro z A hA v
    rw [Matrix.smul_mulVec, differential_smul, hA, mul_zero]

theorem checked_mem_annihilator (M : SparseMatrixCertificate.Code n) (p : Code n)
    (h : checkZero (act M p) = true) :
    SparseMatrixCertificate.realize R M ∈ annihilator p := by
  intro v
  rw [← eval_act]
  exact checkZero_sound _ h v

end Math.SparseCubicCertificate
