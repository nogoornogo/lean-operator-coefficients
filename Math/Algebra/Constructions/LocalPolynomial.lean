import Math.Algebra.Jets.MixedJetParity
import Math.Algebra.Variational.VariationalIBP

/-! Finite local polynomial syntax. Labels and actual mixed jets are reused;
words record arbitrarily high ordinary derivatives without a truncation. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
open MixedJetAlgebra
variable {F B I : Type*}

abbrev Field (F B : Type*) := F ⊕ B
abbrev A (F B I : Type*) := MixedJetAlgebra.Algebra F B I
abbrev D (i : I) : A F B I →ₗ[ℂ] A F B I := totalDerivative i

@[reducible] local instance : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance : Module ℂ (A F B I) := inferInstance
@[reducible] local instance : Ring (A F B I) := inferInstance

inductive Expr (F B I : Type*)
  | constant : ℂ → Expr F B I
  | jet : Field F B → List I → Expr F B I
  | add : Expr F B I → Expr F B I → Expr F B I
  | mul : Expr F B I → Expr F B I → Expr F B I

namespace Expr
instance : Add (Expr F B I) := ⟨Expr.add⟩
instance : Mul (Expr F B I) := ⟨Expr.mul⟩
instance : Neg (Expr F B I) := ⟨fun p => constant (-1) * p⟩
instance : Sub (Expr F B I) := ⟨fun p q => p + -q⟩
instance (n : ℕ) : OfNat (Expr F B I) n := ⟨constant n⟩
instance : SMul ℂ (Expr F B I) := ⟨fun c p => constant c * p⟩
def power (p : Expr F B I) : ℕ → Expr F B I
  | 0 => constant 1
  | n+1 => power p n * p
instance : Pow (Expr F B I) ℕ := ⟨power⟩

theorem smul_def (c : ℂ) (p : Expr F B I) : c • p = constant c * p := rfl
theorem neg_def (p : Expr F B I) : -p = constant (-1) * p := rfl
@[simp] theorem pow_zero (p : Expr F B I) : p^0 = constant 1 := rfl
@[simp] theorem pow_succ (p : Expr F B I) (n : ℕ) : p^(n+1) = p^n*p := rfl

def fermion (f : F) : Expr F B I := jet (.inl f) []
def boson (b : B) : Expr F B I := jet (.inr b) []

def sum (ps : List (Expr F B I)) : Expr F B I := ps.foldr (·+·) (constant 0)

def derivative (i : I) : Expr F B I → Expr F B I
  | constant _ => constant 0
  | jet s w => jet s (i :: w)
  | add p q => derivative i p + derivative i q
  | mul p q => derivative i p*q + p*derivative i q

def wordIndex : List I → (I →₀ ℕ)
  | [] => 0
  | i :: w => wordIndex w + Finsupp.single i 1

def eval : Expr F B I → A F B I
  | constant c => algebraMap ℂ _ c
  | jet (.inl f) w => odd (f, wordIndex w)
  | jet (.inr b) w => even (b, wordIndex w)
  | add p q => eval p + eval q
  | mul p q => eval p * eval q

@[simp] theorem eval_add (p q : Expr F B I) : (p+q).eval = p.eval+q.eval := rfl
@[simp] theorem eval_mul (p q : Expr F B I) : (p*q).eval = p.eval*q.eval := rfl
theorem eval_sum (ps : List (Expr F B I)) : (sum ps).eval = (ps.map eval).sum := by
  induction ps with
  | nil => exact map_zero _
  | cons p ps ih => exact congrArg (fun q => p.eval+q) ih
@[simp] theorem eval_neg (p : Expr F B I) : (-p).eval = -p.eval := by
  change algebraMap ℂ _ (-1) * p.eval = -p.eval
  rw [map_neg, map_one, neg_one_mul]
@[simp] theorem eval_smul (c : ℂ) (p : Expr F B I) : (c • p).eval = c • p.eval := by
  exact (Algebra.smul_def c p.eval).symm
@[simp] theorem eval_pow (p : Expr F B I) (n : ℕ) : (p^n).eval = p.eval^n := by
  induction n with
  | zero => change algebraMap ℂ _ 1 = p.eval^0; rw [map_one, _root_.pow_zero]
  | succ n ih => change (p^n).eval * p.eval = p.eval^(n+1); rw [ih, _root_.pow_succ]

theorem eval_derivative (i : I) (p : Expr F B I) :
    (derivative i p).eval = D i p.eval := by
  induction p with
  | constant c => simp [derivative, eval, D, Algebra.algebraMap_eq_smul_one]
  | jet s w => cases s <;> simp [derivative, eval, wordIndex, D, ScalarJetAlgebra.shift]
  | add p q hp hq => simp only [derivative, eval, map_add, hp, hq]
  | mul p q hp hq => simp only [derivative, eval, hp, hq, D, totalDerivative_mul]

theorem eval_jet_word (s : Field F B) (w : List I) :
    (jet s w : Expr F B I).eval = VariationalIBP.word D w (jet s []).eval := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [← show derivative i (jet s w) = jet s (i::w) from rfl,
      eval_derivative, ih]; rfl

def parity : Expr F B I → Expr F B I
  | constant c => constant c
  | jet (.inl f) w => -jet (.inl f) w
  | jet (.inr b) w => jet (.inr b) w
  | add p q => parity p + parity q
  | mul p q => parity p * parity q

theorem eval_parity (p : Expr F B I) : (parity p).eval = MixedJetParity.involute p.eval := by
  induction p with
  | constant c => simp [parity, eval]
  | jet s w => cases s <;> simp [parity, eval, eval_neg]
  | add p q hp hq => simp only [parity, eval, map_add, hp, hq]
  | mul p q hp hq => simp only [parity, eval, map_mul, hp, hq]

/-- An even first variation; odd fields have odd variation components. -/
def variation (eta : Field F B → A F B I) : Expr F B I → A F B I
  | constant _ => 0
  | jet s w => VariationalIBP.word D w (eta s)
  | add p q => variation eta p + variation eta q
  | mul p q => variation eta p * q.eval + p.eval * variation eta q

theorem variation_derivative (eta : Field F B → A F B I) (i : I) (p : Expr F B I) :
    (derivative i p).variation eta = D i (p.variation eta) := by
  induction p with
  | constant c => exact (map_zero _).symm
  | jet s w => rfl
  | add p q hp hq => simp only [derivative, variation, hp, hq, map_add]
  | mul p q hp hq =>
    simp only [derivative, variation, eval_derivative, hp, hq, D, map_add,
      MixedJetAlgebra.totalDerivative_mul]
    abel

/-- Comparison with an actual evolutionary derivation, rather than an
assumed first-variation identity for a particular Lagrangian. -/
theorem variation_agrees (delta : A F B I →ₗ[ℂ] A F B I)
    (hC : ∀ c, delta (algebraMap ℂ _ c) = 0)
    (hM : ∀ p q, delta (p*q) = delta p*q + p*delta q)
    (hD : ∀ i p, delta (D i p) = D i (delta p))
    (eta : Field F B → A F B I)
    (hF : ∀ s, delta (jet s []).eval = eta s) (p : Expr F B I) :
    p.variation eta = delta p.eval := by
  have hw (s : Field F B) (w : List I) :
      delta (VariationalIBP.word D w (jet s []).eval) =
        VariationalIBP.word D w (eta s) := by
    induction w with
    | nil => exact hF s
    | cons i w ih => simp only [VariationalIBP.word, hD, ih]
  induction p with
  | constant c => exact (hC c).symm
  | jet s w => rw [variation, eval_jet_word, hw]
  | add p q hp hq => simp only [variation, eval, map_add, hp, hq]
  | mul p q hp hq => simp only [variation, eval, hM, hp, hq]

end Expr

def twist (s : Field F B) (p : A F B I) : A F B I :=
  match s with
  | .inl _ => MixedJetParity.involute p
  | .inr _ => p

def PreservesParity (eta : Field F B → A F B I) : Prop :=
  (∀ f, MixedJetParity.involute (eta (.inl f)) = -eta (.inl f)) ∧
  (∀ b, MixedJetParity.involute (eta (.inr b)) = eta (.inr b))

theorem involute_word (w : List I) (p : A F B I) :
    MixedJetParity.involute (VariationalIBP.word D w p) =
      VariationalIBP.word D w (MixedJetParity.involute p) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [VariationalIBP.word, D, MixedJetParity.involute_derivative, ih]

theorem word_neg (w : List I) (p : A F B I) :
    VariationalIBP.word D w (-p) = -VariationalIBP.word D w p := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [VariationalIBP.word, ih, map_neg]

theorem slide (eta : Field F B → A F B I) (h : PreservesParity eta)
    (s : Field F B) (w : List I) (p : Expr F B I) :
    p.eval * VariationalIBP.word D w (eta s) =
      VariationalIBP.word D w (eta s) * twist s p.eval := by
  have ho (f : F) : MixedJetParity.involute (VariationalIBP.word D w (eta (.inl f))) =
      -VariationalIBP.word D w (eta (.inl f)) := by rw [involute_word, h.1, word_neg]
  have he (b : B) : MixedJetParity.involute (VariationalIBP.word D w (eta (.inr b))) =
      VariationalIBP.word D w (eta (.inr b)) := by rw [involute_word, h.2]
  induction p with
  | constant c =>
    change algebraMap ℂ _ c * _ = _ * twist s (algebraMap ℂ _ c)
    cases s <;> simp only [twist, AlgHom.commutes]
    all_goals exact Algebra.commutes c _
  | jet t v =>
    cases t with
    | inl f =>
      have hs := MixedJetParity.odd_slide (f, Expr.wordIndex v)
        (VariationalIBP.word D w (eta s))
      cases s with
      | inl g =>
        change odd (f, Expr.wordIndex v) * _ = _ * MixedJetParity.involute (odd (f, Expr.wordIndex v))
        rw [MixedJetParity.involute_odd, mul_neg]
        simpa only [ho, neg_mul] using hs
      | inr b => simpa [Expr.eval, twist, he] using hs
    | inr b =>
      cases s <;> simpa [Expr.eval, twist] using
        MixedJetParity.even_central (b, Expr.wordIndex v) (VariationalIBP.word D w (eta _))
  | add p q hp hq => cases s <;> simp_all only [Expr.eval, twist, map_add, add_mul, mul_add]
  | mul p q hp hq =>
    cases s <;> simp_all only [Expr.eval, twist, map_mul]
    all_goals rw [mul_assoc, hq, ← mul_assoc, hp, mul_assoc]

end
end Math.LocalPolynomial
