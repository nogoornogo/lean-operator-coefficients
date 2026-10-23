import Math.RepresentationTheory.Lagrangian.BosonicLagrangianInput
import Math.RepresentationTheory.Jets.DerivativeLiteratureHiggs

/-! Generated Higgs component equations, with every formal conjugate varied.
Physical action and reality dictionaries are independent of these identities. -/
namespace Math.HiggsLagrangianInput
set_option autoImplicit false
noncomputable section
open LocalPolynomial LocalPolynomial.Expr
open DerivativeLiteratureHiggs

abbrev E := Expr Empty Label (Fin 4)
def phi (c : Bool) (i : Fin 2) : E := boson (c,i)
def radius : E := phi true 0*phi false 0+phi true 1*phi false 1
def pair (i : Fin 4) : E :=
  derivative i (phi true 0)*derivative i (phi false 0)+
  derivative i (phi true 1)*derivative i (phi false 1)
def kinetic : E := pair 0-pair 1-pair 2-pair 3
def density (a b : ℂ) : E := kinetic-a • radius-(b/2) • radius^2

theorem phi_eval (c : Bool) (i : Fin 2) : (phi c i).scalarEval = h c i := by
  simp only [phi, boson, scalarEval, Expr.eval, wordIndex, scalarProjection_even]
  rfl

theorem eval_mul (p q : E) : (p*q).scalarEval = p.scalarEval*q.scalarEval := by
  simp only [scalarEval,Expr.eval_mul,map_mul]

theorem radius_eval : radius.scalarEval = rho := by
  simp only [radius,scalarEval_add,eval_mul,phi_eval]
  rfl

theorem pair_eval (i : Fin 4) : (pair i).scalarEval =
    D i (h true 0)*D i (h false 0)+D i (h true 1)*D i (h false 1) := by
  simp only [pair,scalarEval_add,eval_mul,scalarEval_derivative,phi_eval]

theorem kinetic_eval : kinetic.scalarEval = DerivativeLiteratureHiggs.kinetic := by
  simp only [kinetic,scalarEval_sub,pair_eval]
  unfold DerivativeLiteratureHiggs.kinetic DerivativeLiteratureHiggs.pair
  ring

theorem density_eval (a b : ℂ) : (density a b).scalarEval =
    DerivativeLiteratureHiggs.kinetic-a • rho-(b/2) • rho^2 := by
  simp only [density,scalarEval_sub,scalarEval_smul,scalarEval_pow,
    kinetic_eval,radius_eval]

theorem generated_equation (a b : ℂ) (j : Label) :
    (density a b).scalarEuler j = -seed a b (!j.1,j.2) := by
  have hc : (MvPolynomial.C (b*(1/2)) : A)*2 = MvPolynomial.C b := by
    have he : (b*(1/2):ℂ)*2 = b := by ring
    simpa only [map_mul, map_ofNat] using congrArg (MvPolynomial.C (σ := ScalarJetAlgebra.Index Label (Fin 4))) he
  obtain ⟨c,i⟩ := j
  simp only [density, scalarEuler_sub, scalarEuler_smul,
    kinetic, scalarEuler_sub]
  cases c <;> fin_cases i <;>
    simp [pair, radius, phi, boson, derivative,
      scalarEuler, Expr.euler, linearize, eulerTerms,
      Expr.eval, twist, VariationalIBP.adjoint, wordIndex,
      scalarProjection_even,
      ScalarJetAlgebra.totalDerivative_X, ScalarJetAlgebra.shift,
      seed, box, h, rho, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  all_goals
    simp only [div_eq_mul_inv,one_mul] at hc ⊢
    first
    | have he := congrArg (fun q : A => -(h true 0*rho)*q) hc
      simp only [h,rho] at he
      linear_combination he
    | have he := congrArg (fun q : A => -(h true 1*rho)*q) hc
      simp only [h,rho] at he
      linear_combination he
    | have he := congrArg (fun q : A => -(h false 0*rho)*q) hc
      simp only [h,rho] at he
      linear_combination he
    | have he := congrArg (fun q : A => -(h false 1*rho)*q) hc
      simp only [h,rho] at he
      linear_combination he

theorem generated_ideal (a b : ℂ) :
    DifferentialEquation.ideal D (density a b).scalarSeeds =
      DifferentialEquation.ideal D (seeds a b) := by
  apply le_antisymm
  · apply DifferentialEquation.minimal
    · rintro p ⟨j,rfl⟩
      rw [generated_equation]
      exact (DifferentialEquation.ideal D (seeds a b)).neg_mem
        (DifferentialEquation.seed_mem D _ ⟨_,rfl⟩)
    · exact fun i p hp => DifferentialEquation.stable D _ i hp
  · apply DifferentialEquation.minimal
    · rintro p ⟨j,rfl⟩
      have hm := DifferentialEquation.seed_mem D (density a b).scalarSeeds
        (show (density a b).scalarEuler (!j.1,j.2) ∈ (density a b).scalarSeeds from ⟨_,rfl⟩)
      rw [generated_equation] at hm
      simpa using (DifferentialEquation.ideal D (density a b).scalarSeeds).neg_mem hm
    · exact fun i p hp => DifferentialEquation.stable D _ i hp

theorem generated_relations (a b : ℂ) :
    DifferentialEquation.combined D (density a b).scalarSeeds =
      DifferentialEquation.combined D (seeds a b) := by
  unfold DifferentialEquation.combined DifferentialEquation.relations
  rw [generated_ideal]

def input (a b : ℂ) := (density a b).scalarTrivialInput

def toDirect (a b : ℂ) (f : (input a b).Coefficient) :
    (DerivativeLiteratureHiggs.input a b).Coefficient := ⟨f.val, by
  intro p hp
  apply f.property
  change p ∈ DifferentialEquation.combined D (density a b).scalarSeeds
  rw [generated_relations]
  exact hp⟩

def toGenerated (a b : ℂ) (f : (DerivativeLiteratureHiggs.input a b).Coefficient) :
    (input a b).Coefficient := ⟨f.val, by
  intro p hp
  apply f.property
  change p ∈ DifferentialEquation.combined D (seeds a b)
  rw [← generated_relations]
  exact hp⟩

def coefficientEquiv (a b : ℂ) : (input a b).Coefficient ≃ₗ[ℂ]
    (DerivativeLiteratureHiggs.input a b).Coefficient where
  toFun := toDirect a b
  invFun := toGenerated a b
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extraction (a b : ℂ) (f : (input a b).Coefficient) (p : A) :
    (coefficientEquiv a b f).val p = f.val p := rfl

theorem higgs_relation (a b : ℂ) (f : (input a b).Coefficient) :
    f.val redundant = (1/2:ℂ)*f.val qBox+a*f.val (rho^2)+b*f.val (rho^3) :=
  normalized_relation a b (toDirect a b f)

end
end Math.HiggsLagrangianInput
