import Math.RepresentationTheory.Weights.SparseWeightPolynomial

/-! Three equal slots in one transition, with a fixed degree truncation.
All identities are against the original exterior recurrence. -/
namespace Math.GroupedExteriorPolynomial
set_option autoImplicit false
open ComputableWeightPolynomial
open SparseWeightPolynomial (merge)

def scaledShift {W : Type*} [Add W] (w : W) (c : ℤ) (p : Terms W) : Terms W :=
  p.map (fun x => (w+x.1,c*x.2))

def tripleStep {W : Type*} [Ord W] [Add W] (w : W) (rows : List (Terms W)) : ℕ → Terms W
  | 0 => rows.getD 0 []
  | 1 => merge (rows.getD 1 []) (scaledShift w 3 (rows.getD 0 []))
  | 2 => merge (rows.getD 2 []) (merge (scaledShift w 3 (rows.getD 1 []))
      (scaledShift (w+w) 3 (rows.getD 0 [])))
  | n+3 => merge (rows.getD (n+3) []) (merge (scaledShift w 3 (rows.getD (n+2) []))
      (merge (scaledShift (w+w) 3 (rows.getD (n+1) []))
        (shift (w+w+w) (rows.getD n []))))

def rows {W : Type*} [Ord W] [AddZeroClass W] (cap : ℕ) (ws : List W) : List (Terms W) :=
  List.rec (motive := fun _ => List (Terms W)) ([(0,1)] :: List.replicate cap [])
    (fun w _ prev => List.ofFn (fun i : Fin (cap+1) => tripleStep w prev i.val)) ws

def slots {W : Type*} (ws : List W) : List W := ws.flatMap (fun w => [w,w,w])

theorem evaluate_scaledShift {W R : Type*} [Add W] [CommRing R]
    (chi : W → R) (hm : ∀ a b, chi (a+b) = chi a * chi b)
    (w : W) (c : ℤ) (p : Terms W) :
    evaluate chi (scaledShift w c p) = (c : R) * chi w * evaluate chi p := by
  induction p with
  | nil => simp [scaledShift,evaluate]
  | cons x p ih =>
    simpa [scaledShift,evaluate,hm,mul_add,Int.cast_mul,mul_comm,mul_left_comm,mul_assoc] using ih

theorem tripleStep_evaluation {W R : Type*} [Ord W] [Std.LawfulEqOrd W]
    [AddZeroClass W] [CommRing R] (chi : W → R)
    (hm : ∀ a b, chi (a+b) = chi a * chi b)
    (w : W) (ws : List W) (prev : List (Terms W)) (n : ℕ)
    (h : ∀ k, k ≤ n → evaluate chi (prev.getD k []) = evaluate chi (exterior ws k)) :
    evaluate chi (tripleStep w prev n) = evaluate chi (exterior (w::w::w::ws) n) := by
  rcases n with _ | _ | _ | n
  all_goals simp only [tripleStep,SparseWeightPolynomial.evaluate_merge,
    evaluate_scaledShift chi hm,evaluate_shift chi hm,hm]
  all_goals simp (disch := omega) only [h,exterior,evaluate_append,evaluate_shift chi hm]
  all_goals ring

theorem rows_evaluation {W R : Type*} [Ord W] [Std.LawfulEqOrd W]
    [AddZeroClass W] [CommRing R] (chi : W → R)
    (hm : ∀ a b, chi (a+b) = chi a * chi b) (cap : ℕ) (ws : List W)
    (n : ℕ) (hn : n ≤ cap) :
    evaluate chi ((rows cap ws).getD n []) = evaluate chi (exterior (slots ws) n) := by
  induction ws generalizing n with
  | nil =>
    cases n with
    | zero => simp [rows,slots,exterior,List.getD]
    | succ n =>
      have hlt : n < cap := by omega
      simp [rows,slots,exterior,List.getD,hlt]
  | cons w ws ih =>
    have hlt : n < cap+1 := by omega
    simp only [rows,List.getD,List.getElem?_ofFn,hlt,dite_true,Option.getD_some]
    change evaluate chi (tripleStep w (rows cap ws) n) = _
    exact tripleStep_evaluation chi hm w (slots ws) _ n (fun k hk => ih k (by omega))

end Math.GroupedExteriorPolynomial
