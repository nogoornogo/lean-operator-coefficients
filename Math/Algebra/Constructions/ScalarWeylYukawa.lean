import Math.Algebra.Constructions.PairedWeylKinetic

/-! A total scalar/Weyl Yukawa density. Its Euler equations are computed after
the kinetic, mass and interaction terms are added. Three even labels of the
existing paired source remain unused spectators. -/
namespace Math.ScalarWeylYukawa
set_option autoImplicit false
noncomputable section
open LocalPolynomial hiding D
open LocalPolynomial.Expr PairedWeylKinetic
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def scalarLabel : Label := (false,0)
def phi : E := boson scalarLabel
def spinor (c : Bool) (a : Fin 2) : E := fermion (c,a)
def pair (c : Bool) : E := spinor c 0 * spinor c 1
def epsilon (c : Bool) (a : Fin 2) : A := if a = 0 then psi c 1 else -psi c 0
def directionalKinetic (i : Fin 4) : E := (1/2 : ℂ) • (derivative i phi)^2
def scalarKinetic : E :=
  directionalKinetic 0-directionalKinetic 1-directionalKinetic 2-directionalKinetic 3
def wave : A := D 0 (D 0 phi.eval)-D 1 (D 1 phi.eval)-
  D 2 (D 2 phi.eval)-D 3 (D 3 phi.eval)
def density (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) : E :=
  scalarKinetic-(massSquared/2) • phi^2+kappa • PairedWeylKinetic.density-
  mass false • pair false-mass true • pair true-
  yukawa false • (phi*pair false)-yukawa true • (phi*pair true)

theorem pair_odd (c : Bool) (j : Label) :
    (pair c).euler (.inl j) = if j.1=c then epsilon c j.2 else 0 := by
  obtain ⟨d,a⟩ := j
  cases c <;> cases d <;> fin_cases a <;>
    simp [pair,spinor,fermion,euler,linearize,eulerTerms,Expr.eval,twist,
      VariationalIBP.adjoint,epsilon,psi,wordIndex]

theorem pair_even (c : Bool) (j : Label) : (pair c).euler (.inr j) = 0 := by
  simp [pair,spinor,fermion,euler,linearize,eulerTerms,Expr.eval,twist,VariationalIBP.adjoint]

theorem interaction_odd (c : Bool) (j : Label) :
    (phi*pair c).euler (.inl j) =
      if j.1=c then phi.eval*epsilon c j.2 else 0 := by
  obtain ⟨d,a⟩ := j
  cases c <;> cases d <;> fin_cases a <;>
    simp [phi,pair,spinor,fermion,boson,euler,linearize,eulerTerms,Expr.eval,twist,
      VariationalIBP.adjoint,epsilon,psi,wordIndex]

theorem interaction_even (c : Bool) (j : Label) :
    (phi*pair c).euler (.inr j) = if j=scalarLabel then (pair c).eval else 0 := by
  classical
  simp [phi,pair,spinor,fermion,boson,euler,linearize,eulerTerms,Expr.eval,twist,
    VariationalIBP.adjoint,Finsupp.single_apply,eq_comm]

theorem phi_squared_even (j : Label) :
    (phi^2).euler (.inr j) = if j=scalarLabel then (2:ℂ) • phi.eval else 0 := by
  classical
  simp [phi,boson,euler,linearize,eulerTerms,Expr.eval,twist,VariationalIBP.adjoint,
    Finsupp.single_apply,eq_comm,two_smul]
  split_ifs <;> first | rfl | simp_all only [← Algebra.TensorProduct.one_def,one_mul]

theorem phi_squared_odd (j : Label) : (phi^2).euler (.inl j) = 0 := by
  simp [phi,boson,euler,linearize,eulerTerms,Expr.eval,twist,VariationalIBP.adjoint]

theorem directional_even (i : Fin 4) (j : Label) :
    (directionalKinetic i).euler (.inr j) =
      if j=scalarLabel then -D i (D i phi.eval) else 0 := by
  classical
  rw [directionalKinetic,euler_smul,Finsupp.smul_apply]
  have he : ((derivative i phi)^2).euler (.inr j) =
      if j=scalarLabel then -(2:ℂ) • D i (D i phi.eval) else 0 := by
    by_cases hj : j=scalarLabel
    · subst j
      simp [phi,derivative,boson,euler,linearize,eulerTerms,Expr.eval,twist,
        VariationalIBP.adjoint,wordIndex,← Algebra.TensorProduct.one_def]
      simp [ScalarJetAlgebra.shift,two_smul]
    · simp [phi,derivative,boson,euler,linearize,eulerTerms,Expr.eval,twist,
        VariationalIBP.adjoint,hj]
  rw [he]
  split_ifs <;> simp [smul_smul]

theorem directional_odd (i : Fin 4) (j : Label) :
    (directionalKinetic i).euler (.inl j) = 0 := by
  simp [directionalKinetic,Expr.smul_def,phi,derivative,boson,euler,linearize,eulerTerms,Expr.eval,twist,
    VariationalIBP.adjoint]

theorem scalar_kinetic_even (j : Label) : scalarKinetic.euler (.inr j) =
    if j=scalarLabel then -wave else 0 := by
  simp only [scalarKinetic,euler_sub,directional_even,Finsupp.sub_apply]
  split_ifs <;> simp only [wave,sub_self]
  abel

theorem scalar_kinetic_odd (j : Label) : scalarKinetic.euler (.inl j) = 0 := by
  simp [scalarKinetic,euler_sub,directional_odd]

def oddEquation (kappa : ℂ) (mass yukawa : Bool → ℂ) (j : Label) : A :=
  kappa • seed (!j.1,j.2)-mass j.1 • epsilon j.1 j.2-
    yukawa j.1 • (phi.eval*epsilon j.1 j.2)
def evenEquation (massSquared : ℂ) (yukawa : Bool → ℂ) : A :=
  -wave-massSquared • phi.eval-yukawa false • (pair false).eval-yukawa true • (pair true).eval

theorem generated_odd (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) (j : Label) :
    (density kappa massSquared mass yukawa).euler (.inl j) = oddEquation kappa mass yukawa j := by
  obtain ⟨c,a⟩ := j
  cases c <;>
    simp only [density,euler_sub,euler_add,euler_smul,Finsupp.sub_apply,Finsupp.add_apply,
      Finsupp.smul_apply,scalar_kinetic_odd,phi_squared_odd,
      PairedWeylKinetic.generated_odd,pair_odd,interaction_odd,oddEquation,
      Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,smul_zero,sub_zero,zero_add]

theorem generated_even (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) (j : Label) :
    (density kappa massSquared mass yukawa).euler (.inr j) =
      if j=scalarLabel then evenEquation massSquared yukawa else 0 := by
  classical
  simp only [density,euler_sub,euler_add,euler_smul,Finsupp.sub_apply,Finsupp.add_apply,
    Finsupp.smul_apply,scalar_kinetic_even,phi_squared_even,PairedWeylKinetic.generated_even,
    pair_even,interaction_even,smul_zero,sub_zero,add_zero]
  split_ifs <;> simp [evenEquation,smul_smul]

theorem zero_yukawa (kappa massSquared : ℂ) (mass : Bool → ℂ) (j : Label) :
    (density kappa massSquared mass (fun _ => 0)).euler (.inl j) =
      kappa • seed (!j.1,j.2)-mass j.1 • epsilon j.1 j.2 := by
  simp [generated_odd,oddEquation]

end
end Math.ScalarWeylYukawa
