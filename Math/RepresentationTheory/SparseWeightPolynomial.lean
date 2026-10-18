import Math.RepresentationTheory.ComputableWeightPolynomial
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! Aggregated sorted merges and a shared exterior-degree table.
Semantic preservation does not assume ordering or uniqueness certificates. -/
namespace Math.SparseWeightPolynomial
set_option autoImplicit false
open ComputableWeightPolynomial

/-- Structural recursion avoids accessibility proofs during kernel reduction.
The concatenating fallback preserves evaluation even with insufficient fuel. -/
def mergeFuel {W : Type*} [Ord W] (n : ℕ) (p q : Terms W) : Terms W :=
  Nat.rec (motive := fun _ => Terms W → Terms W → Terms W)
    (fun p q => p ++ q)
    (fun _ recur p q => match p,q with
      | [],q => q
      | p,[] => p
      | a::p,b::q => match compare a.1 b.1 with
        | .lt => a :: recur p (b::q)
        | .gt => b :: recur (a::p) q
        | .eq => (a.1,a.2+b.2) :: recur p q) n p q

def merge {W : Type*} [Ord W] (p q : Terms W) : Terms W :=
  mergeFuel (p.length+q.length) p q

theorem mergeFuel_cons {W : Type*} [Ord W] (n : ℕ) (a b : W × ℤ) (p q : Terms W) :
    mergeFuel (n+1) (a::p) (b::q) = match compare a.1 b.1 with
      | .lt => a :: mergeFuel n p (b::q)
      | .gt => b :: mergeFuel n (a::p) q
      | .eq => (a.1,a.2+b.2) :: mergeFuel n p q := rfl

theorem evaluate_mergeFuel {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [CommRing R]
    (chi : W → R) (n : ℕ) (p q : Terms W) :
    evaluate chi (mergeFuel n p q) = evaluate chi p + evaluate chi q := by
  induction n generalizing p q with
  | zero => simp [mergeFuel,evaluate_append]
  | succ n ih =>
    cases p with
    | nil => simp [mergeFuel,evaluate]
    | cons a p =>
      cases q with
      | nil => simp [mergeFuel,evaluate]
      | cons b q =>
        rw [mergeFuel_cons]
        cases h : compare a.1 b.1
        all_goals simp_all [evaluate,Int.cast_add,add_mul]
        all_goals abel

theorem evaluate_merge {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [CommRing R]
    (chi : W → R) (p q : Terms W) :
    evaluate chi (merge p q) = evaluate chi p + evaluate chi q := by
  exact evaluate_mergeFuel chi _ p q

@[simp] theorem merge_nil_right {W : Type*} [Ord W] (p : Terms W) : merge p [] = p := by
  cases p <;> simp [merge,mergeFuel]

@[simp] theorem merge_nil_left {W : Type*} [Ord W] (p : Terms W) : merge [] p = p := by
  cases p <;> simp [merge,mergeFuel]

def multiply {W : Type*} [Ord W] [Add W] (p q : Terms W) : Terms W :=
  p.foldr (fun x acc => merge (q.map (fun y => (x.1+y.1,x.2*y.2))) acc) []

theorem evaluate_multiply {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [Add W] [CommRing R]
    (chi : W → R) (hm : ∀ a b, chi (a+b) = chi a * chi b) (p q : Terms W) :
    evaluate chi (multiply p q) = evaluate chi p * evaluate chi q := by
  induction p with
  | nil => simp [multiply,evaluate]
  | cons x p ih =>
    simp only [multiply,List.foldr_cons,evaluate_merge]
    have h : evaluate chi (q.map (fun y => (x.1+y.1,x.2*y.2))) =
        (x.2 : R) * chi x.1 * evaluate chi q := by
      clear ih
      induction q with
      | nil => simp [evaluate]
      | cons y q ihq =>
        simpa [evaluate,hm,mul_add,Int.cast_mul,mul_comm,mul_left_comm,mul_assoc] using ihq
    rw [h]
    change _ + evaluate chi (multiply p q) = _
    rw [ih]
    simp [evaluate,add_mul,mul_assoc]

def multiplyFast {W : Type*} [Ord W] [Add W] (p q : Terms W) : Terms W :=
  if p.length ≤ q.length then multiply p q else multiply q p

theorem multiply_one_left {W : Type*} [Ord W] [AddZeroClass W] (p : Terms W) :
    multiply [(0,1)] p = p := by
  simp [multiply]

@[simp] theorem multiplyFast_one_left {W : Type*} [Ord W] [AddZeroClass W] (p : Terms W) :
    multiplyFast [(0,1)] p = p := by
  cases p with
  | nil => simp [multiplyFast,multiply]
  | cons x p => simp [multiplyFast,multiply_one_left]

@[simp] theorem multiplyFast_one_right {W : Type*} [Ord W] [AddZeroClass W] (p : Terms W) :
    multiplyFast p [(0,1)] = p := by
  cases p with
  | nil => simp [multiplyFast,multiply]
  | cons x p =>
    cases p with
    | nil => simp [multiplyFast,multiply]
    | cons y p =>
      simp [multiplyFast,multiply_one_left]

theorem evaluate_multiplyFast {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [Add W] [CommRing R]
    (chi : W → R) (hm : ∀ a b, chi (a+b) = chi a * chi b) (p q : Terms W) :
    evaluate chi (multiplyFast p q) = evaluate chi p * evaluate chi q := by
  unfold multiplyFast
  split <;> simp [evaluate_multiply chi hm,mul_comm]

def product {W : Type*} [Ord W] [AddZeroClass W] : List (Terms W) → Terms W
  | [] => [(0,1)]
  | p::ps => multiplyFast p (product ps)

def normalize {W : Type*} [Ord W] (p : Terms W) : Terms W :=
  p.foldr (fun x acc => merge [x] acc) []

theorem evaluate_normalize {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [CommRing R]
    (chi : W → R) (p : Terms W) : evaluate chi (normalize p) = evaluate chi p := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    change evaluate chi (merge [x] (normalize p)) = evaluate chi (x::p)
    rw [evaluate_merge,ih]
    simp [evaluate]

theorem evaluate_product {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [AddZeroClass W] [CommRing R]
    (chi : W → R) (h0 : chi 0 = 1) (hm : ∀ a b, chi (a+b) = chi a * chi b) (ps : List (Terms W)) :
    evaluate chi (product ps) = (ps.map (evaluate chi)).prod := by
  induction ps with
  | nil => simp [product,evaluate,h0]
  | cons p ps ih => simp [product,evaluate_multiplyFast chi hm,ih]

def exteriorRows {W : Type*} [Ord W] [AddZeroClass W] (ws : List W) : List (Terms W) :=
  List.rec (motive := fun _ => List (Terms W)) [[(0,1)]]
    (fun w ws rows => List.ofFn (fun i : Fin (ws.length+2) => match i.val with
      | 0 => rows.getD 0 []
      | n+1 => merge (rows.getD (n+1) []) (shift w (rows.getD n [])))) ws

def exterior {W : Type*} [Ord W] [AddZeroClass W] (ws : List W) (n : ℕ) : Terms W :=
  (exteriorRows ws).getD n []

theorem rows_length {W : Type*} [Ord W] [AddZeroClass W] (ws : List W) :
    (exteriorRows ws).length = ws.length+1 := by
  cases ws <;> simp [exteriorRows]

theorem rows_zero {W : Type*} [Ord W] [AddZeroClass W] (ws : List W) :
    (exteriorRows ws).getD 0 [] = [(0,1)] := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [exteriorRows,List.getD] using ih

theorem exterior_evaluation {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [AddZeroClass W] [CommRing R]
    (chi : W → R) (hm : ∀ a b, chi (a+b) = chi a * chi b) (ws : List W) (n : ℕ) :
    evaluate chi (exterior ws n) = evaluate chi (ComputableWeightPolynomial.exterior ws n) := by
  induction ws generalizing n with
  | nil => cases n <;> simp [exterior,exteriorRows,ComputableWeightPolynomial.exterior]
  | cons w ws ih =>
    by_cases hn : n < ws.length+2
    · cases n with
      | zero =>
        simpa [exterior,exteriorRows,List.getD,List.getElem?_ofFn,hn,
          ComputableWeightPolynomial.exterior] using ih 0
      | succ n =>
        simpa only [exterior,exteriorRows,List.getD,List.getElem?_ofFn,hn,dite_true,
          Option.getD_some,evaluate_merge,evaluate_shift chi hm,ComputableWeightPolynomial.exterior,
          evaluate_append] using congrArg₂ (fun x y : R => x + chi w * y) (ih (n+1)) (ih n)
    · have he : ComputableWeightPolynomial.exterior (w::ws) n = [] :=
        exterior_above _ _ (by simp; omega)
      simp [exterior,exteriorRows,List.getD,hn,he,evaluate]

theorem reference_zero {W : Type*} [AddZeroClass W] (ws : List W) :
    ComputableWeightPolynomial.exterior ws 0 = [(0,1)] := by
  induction ws <;> simp_all [ComputableWeightPolynomial.exterior]

def exteriorFast {W : Type*} [Ord W] [AddZeroClass W] (ws : List W) (n : ℕ) : Terms W :=
  if n=0 then [(0,1)] else if ws.length < n then [] else exterior ws n

theorem exteriorFast_evaluation {W R : Type*} [Ord W] [Std.LawfulEqOrd W] [AddZeroClass W] [CommRing R]
    (chi : W → R) (hm : ∀ a b, chi (a+b) = chi a * chi b) (ws : List W) (n : ℕ) :
    evaluate chi (exteriorFast ws n) = evaluate chi (ComputableWeightPolynomial.exterior ws n) := by
  by_cases h0 : n=0
  · subst n; simp [exteriorFast,reference_zero]
  · by_cases hn : ws.length < n
    · simp [exteriorFast,h0,hn,exterior_above ws n hn]
    · simpa [exteriorFast,h0,hn] using exterior_evaluation chi hm ws n

theorem formal_coefficient {W : Type*} [AddCommMonoid W] [DecidableEq W] (p : Terms W) (w : W) :
    (evaluate (fun a => AddMonoidAlgebra.single a (1 : ℤ)) p).coeff w = coefficient p w := by
  classical
  induction p with
  | nil => simp [evaluate,coefficient]
  | cons x p ih =>
    change (((x.2 : AddMonoidAlgebra ℤ W) * AddMonoidAlgebra.single x.1 1 +
      evaluate (fun a => AddMonoidAlgebra.single a (1 : ℤ)) p).coeff w) = _
    rw [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,ih]
    simp [coefficient,AddMonoidAlgebra.intCast_def,AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.coeff_single,Finsupp.single_apply,eq_comm]

end Math.SparseWeightPolynomial
