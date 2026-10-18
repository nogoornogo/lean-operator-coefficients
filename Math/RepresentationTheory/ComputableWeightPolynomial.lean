import Math.RepresentationTheory.ExteriorCharacterPolynomial
import Math.RepresentationTheory.Characters.CompactWeylExtraction

/-! Executable finite weight terms and their proof-only Finsupp presentation.
Repeated terms are intentional: the reference recurrence needs no sorting oracle. -/
namespace Math.ComputableWeightPolynomial
set_option autoImplicit false
open scoped BigOperators
open Polynomial

abbrev Terms (W : Type*) := List (W × ℤ)

def coefficient {W : Type*} [DecidableEq W] (p : Terms W) (w : W) : ℤ :=
  (p.map (fun x => if x.1 = w then x.2 else 0)).sum

def shift {W : Type*} [Add W] (w : W) (p : Terms W) : Terms W :=
  p.map (fun x => (w + x.1, x.2))

def multiply {W : Type*} [Add W] (p q : Terms W) : Terms W :=
  p.flatMap (fun x => q.map (fun y => (x.1 + y.1, x.2 * y.2)))

def exterior {W : Type*} [AddZeroClass W] : List W → ℕ → Terms W
  | [], 0 => [(0,1)]
  | [], _+1 => []
  | _::ws, 0 => exterior ws 0
  | w::ws, n+1 => exterior ws (n+1) ++ shift w (exterior ws n)

def product {W : Type*} [AddZeroClass W] : List (Terms W) → Terms W
  | [] => [(0,1)]
  | p::ps => multiply p (product ps)

noncomputable def presentation {W : Type*} (p : Terms W) : W →₀ ℤ :=
  (p.map (fun x => Finsupp.single x.1 x.2)).sum

noncomputable def evaluate {W R : Type*} [Ring R] (chi : W → R) (p : Terms W) : R :=
  (p.map (fun x => (x.2 : R) * chi x.1)).sum

theorem presentation_apply {W : Type*} [DecidableEq W] (p : Terms W) (w : W) :
    presentation p w = coefficient p w := by
  classical
  induction p with
  | nil => simp [presentation,coefficient]
  | cons x p ih =>
    simp only [presentation,List.map_cons,List.sum_cons,Finsupp.add_apply]
    rw [show (p.map (fun x => Finsupp.single x.1 x.2)).sum w = coefficient p w from ih]
    simp [coefficient,Finsupp.single_apply,eq_comm]

theorem presentation_evaluate {W R : Type*} [Ring R] (chi : W → R) (p : Terms W) :
    (presentation p).sum (fun w c => (c : R) * chi w) = evaluate chi p := by
  classical
  induction p with
  | nil => simp [presentation,evaluate]
  | cons x p ih =>
    simp only [presentation,List.map_cons,List.sum_cons]
    rw [Finsupp.sum_add_index]
    · simpa [presentation,evaluate] using congrArg (fun r : R => (x.2 : R) * chi x.1 + r) ih
    · intro; simp
    · intros; simp [add_mul]

theorem evaluate_append {W R : Type*} [Ring R] (chi : W → R) (p q : Terms W) :
    evaluate chi (p++q) = evaluate chi p + evaluate chi q := by
  simp [evaluate]

theorem evaluate_shift {W R : Type*} [Add W] [CommRing R] (chi : W → R)
    (hm : ∀ a b, chi (a+b) = chi a * chi b) (w : W) (p : Terms W) :
    evaluate chi (shift w p) = chi w * evaluate chi p := by
  induction p with
  | nil => simp [shift,evaluate]
  | cons x p ih =>
    simpa [shift,evaluate,hm,mul_add,mul_comm,mul_left_comm,mul_assoc] using ih

theorem evaluate_multiply {W R : Type*} [Add W] [CommRing R] (chi : W → R)
    (hm : ∀ a b, chi (a+b) = chi a * chi b) (p q : Terms W) :
    evaluate chi (multiply p q) = evaluate chi p * evaluate chi q := by
  induction p with
  | nil => simp [multiply,evaluate]
  | cons x p ih =>
    simp only [multiply,List.flatMap_cons,evaluate_append]
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

theorem exterior_evaluate {W R : Type*} [AddZeroClass W] [CommRing R]
    (chi : W → R) (h0 : chi 0 = 1) (hm : ∀ a b, chi (a+b) = chi a * chi b)
    (ws : List W) (n : ℕ) :
    evaluate chi (exterior ws n) =
      ((ws.map (fun w => (1 + C (chi w) * X : R[X]))).prod).coeff n := by
  induction ws generalizing n with
  | nil => cases n <;> simp [exterior,evaluate,h0,Polynomial.coeff_one]
  | cons w ws ih =>
    cases n with
    | zero => simp [exterior,ih,Polynomial.mul_coeff_zero]
    | succ n =>
      rw [exterior,evaluate_append,evaluate_shift chi hm,ih,ih]
      simp only [List.map_cons,List.prod_cons,add_mul,one_mul,Polynomial.coeff_add,
        mul_assoc,Polynomial.coeff_C_mul,Polynomial.coeff_X_mul]

theorem exterior_above {W : Type*} [AddZeroClass W] (ws : List W) (n : ℕ)
    (hn : ws.length < n) : exterior ws n = [] := by
  induction ws generalizing n with
  | nil => cases n <;> simp_all [exterior]
  | cons w ws ih =>
    cases n with
    | zero => simp_all
    | succ n =>
      simp only [List.length_cons,Nat.succ_lt_succ_iff] at hn
      simp [exterior,ih n hn,ih (n+1) (by omega),shift]

theorem evaluate_product {W R : Type*} [AddZeroClass W] [CommRing R] (chi : W → R)
    (h0 : chi 0 = 1) (hm : ∀ a b, chi (a+b) = chi a * chi b) (ps : List (Terms W)) :
    evaluate chi (product ps) = (ps.map (evaluate chi)).prod := by
  induction ps with
  | nil => simp [product,evaluate,h0]
  | cons p ps ih => simp [product,evaluate_multiply chi hm,ih]

theorem exterior_length {W : Type*} [AddZeroClass W] (ws : List W) (n : ℕ) :
    (exterior ws n).length = ws.length.choose n := by
  induction ws generalizing n with
  | nil => cases n <;> simp [exterior]
  | cons w ws ih =>
    cases n with
    | zero => simp [exterior,ih]
    | succ n => simp [exterior,shift,ih,Nat.choose_succ_succ,add_comm]

theorem exterior_ofFn_evaluate {W R : Type*} [AddZeroClass W] [CommRing R]
    {d : ℕ} (chi : W → R) (h0 : chi 0 = 1)
    (hm : ∀ a b, chi (a+b) = chi a * chi b) (ws : Fin d → W) (n : ℕ) :
    evaluate chi (exterior (List.ofFn ws) n) =
      (ExteriorCharacterPolynomial.generating (fun i => chi (ws i))).coeff n := by
  rw [exterior_evaluate chi h0 hm,List.map_ofFn,List.prod_ofFn]
  rfl

end Math.ComputableWeightPolynomial
