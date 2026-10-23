import Math.Algebra.Constructions.LocalPolynomial

/-! Automatic variation coefficients, word adjoints, Euler expressions and
currents. No caller-supplied equation or first-variation formula is used. -/
namespace Math.LocalPolynomial
set_option autoImplicit false
noncomputable section
variable {F B I : Type*}
@[reducible] local instance : AddCommGroup (A F B I) := inferInstance
@[reducible] local instance : Module ℂ (A F B I) := inferInstance
@[reducible] local instance : Ring (A F B I) := inferInstance

structure Term (F B I : Type*) where
  field : Field F B
  derivatives : List I
  coefficient : A F B I

def linearize : Expr F B I → List (Term F B I)
  | .constant _ => []
  | .jet s w => [⟨s, w, 1⟩]
  | .add p q => linearize p ++ linearize q
  | .mul p q =>
      (linearize p).map (fun t => {t with coefficient := t.coefficient*q.eval}) ++
      (linearize q).map (fun t => {t with coefficient := twist t.field p.eval*t.coefficient})

def linearized (eta : Field F B → A F B I) : List (Term F B I) → A F B I
  | [] => 0
  | t :: ts => VariationalIBP.word D t.derivatives (eta t.field)*t.coefficient + linearized eta ts

theorem linearized_append (eta : Field F B → A F B I) (ts us : List (Term F B I)) :
    linearized eta (ts++us) = linearized eta ts + linearized eta us := by
  induction ts with
  | nil => simp [linearized]
  | cons t ts ih => simp only [List.cons_append, linearized, ih, add_assoc]

theorem linearized_right (eta : Field F B → A F B I) (ts : List (Term F B I)) (q : A F B I) :
    linearized eta (ts.map (fun t => {t with coefficient := t.coefficient*q})) =
      linearized eta ts * q := by
  induction ts with
  | nil => simp [linearized]
  | cons t ts ih => simp [linearized, ih, add_mul, mul_assoc]

theorem linearized_left (eta : Field F B → A F B I) (h : PreservesParity eta)
    (ts : List (Term F B I)) (p : Expr F B I) :
    linearized eta (ts.map (fun t => {t with coefficient := twist t.field p.eval*t.coefficient})) =
      p.eval * linearized eta ts := by
  induction ts with
  | nil => simp [linearized]
  | cons t ts ih =>
    simp only [List.map_cons, linearized, ih, mul_add]
    rw [← mul_assoc, ← slide eta h t.field t.derivatives p, mul_assoc]

theorem linearize_correct (eta : Field F B → A F B I) (h : PreservesParity eta)
    (p : Expr F B I) : p.variation eta = linearized eta (linearize p) := by
  induction p with
  | constant c => rfl
  | jet s w => simp [Expr.variation, linearize, linearized]
  | add p q hp hq => simp only [Expr.variation, linearize, linearized_append, hp, hq]
  | mul p q hp hq =>
    simp only [Expr.variation, linearize, linearized_append, linearized_right,
      linearized_left eta h, hp, hq]

def leftMul (p : A F B I) : A F B I →ₗ[ℂ] A F B I where
  toFun q := p*q
  map_add' _ _ := mul_add _ _ _
  map_smul' _ _ := mul_smul_comm _ _ _

def bulk (eta : Field F B → A F B I) : (Field F B →₀ A F B I) →ₗ[ℂ] A F B I :=
  Finsupp.lsum ℂ (fun s => leftMul (eta s))

@[simp] theorem bulk_single (eta : Field F B → A F B I) (s : Field F B) (p : A F B I) :
    bulk eta (Finsupp.single s p) = eta s*p := Finsupp.lsum_single _ _ _ _

def eulerTerms : List (Term F B I) → (Field F B →₀ A F B I)
  | [] => 0
  | t :: ts => Finsupp.single t.field (VariationalIBP.adjoint D t.derivatives t.coefficient) + eulerTerms ts

def boundaryTerms (eta : Field F B → A F B I) : List (Term F B I) → (I →₀ A F B I)
  | [] => 0
  | t :: ts => VariationalIBP.current D t.derivatives (eta t.field) t.coefficient + boundaryTerms eta ts

theorem terms_parts (eta : Field F B → A F B I) (ts : List (Term F B I)) :
    linearized eta ts = bulk eta (eulerTerms ts) +
      VariationalIBP.divergence D (boundaryTerms eta ts) := by
  induction ts with
  | nil => simp [linearized, eulerTerms, boundaryTerms]
  | cons t ts ih =>
    simp only [linearized, eulerTerms, boundaryTerms, map_add, bulk_single]
    rw [VariationalIBP.parts D MixedJetAlgebra.totalDerivative_mul, ih]
    abel

namespace Expr
def euler (p : Expr F B I) : Field F B →₀ A F B I := eulerTerms (linearize p)
def boundary (p : Expr F B I) (eta : Field F B → A F B I) : I →₀ A F B I :=
  boundaryTerms eta (linearize p)

theorem first_variation (p : Expr F B I) (eta : Field F B → A F B I)
    (h : PreservesParity eta) :
    p.variation eta = bulk eta p.euler + VariationalIBP.divergence D (p.boundary eta) := by
  rw [linearize_correct eta h, terms_parts]
  rfl

theorem euler_constant (c : ℂ) : (constant c : Expr F B I).euler = 0 := rfl

theorem euler_add (p q : Expr F B I) : (p+q).euler = p.euler+q.euler := by
  change eulerTerms (linearize p ++ linearize q) = _
  have h (ts us : List (Term F B I)) : eulerTerms (ts++us) = eulerTerms ts+eulerTerms us := by
    induction ts with
    | nil => simp [eulerTerms]
    | cons t ts ih => simp only [List.cons_append, eulerTerms, ih, add_assoc]
  exact h _ _

theorem euler_smul (c : ℂ) (p : Expr F B I) : (c • p).euler = c • p.euler := by
  have ht (t : Term F B I) : twist t.field (algebraMap ℂ (A F B I) c)*t.coefficient = c • t.coefficient := by
    cases t.field <;> simp only [twist, AlgHom.commutes]
    all_goals exact (Algebra.smul_def c t.coefficient).symm
  have hl : linearize (c • p) =
      (linearize p).map (fun t => {t with coefficient := c • t.coefficient}) := by
    simp only [smul_def, linearize, List.map_nil, List.nil_append, eval, ht]
  have he (ts : List (Term F B I)) :
      eulerTerms (ts.map (fun t => {t with coefficient := c • t.coefficient})) = c • eulerTerms ts := by
    induction ts with
    | nil => simp [eulerTerms]
    | cons t ts ih => simp [eulerTerms, VariationalIBP.adjoint_smul, ih, smul_add]
  exact (congrArg eulerTerms hl).trans (he _)

theorem euler_neg (p : Expr F B I) : (-p).euler = -p.euler := by
  change ((-1 : ℂ) • p).euler = _
  rw [euler_smul, neg_one_smul]

theorem euler_sub (p q : Expr F B I) : (p-q).euler = p.euler-q.euler := by
  change (p + -q).euler = _
  rw [euler_add, euler_neg, sub_eq_add_neg]

theorem euler_sum (ps : List (Expr F B I)) : (sum ps).euler = (ps.map euler).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => exact (euler_add p (sum ps)).trans (congrArg (fun q => p.euler+q) ih)
end Expr

end
end Math.LocalPolynomial
