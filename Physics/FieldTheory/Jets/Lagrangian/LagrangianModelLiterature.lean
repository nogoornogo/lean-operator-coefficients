import Physics.FieldTheory.Jets.Lagrangian.YukawaDensitySymmetry
import Physics.FieldTheory.Jets.Lagrangian.RegisteredLagrangianModels
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureRecheck

/-! Primary-source consumers of the model API. Paper contractions are
expanded with a fixed component dictionary before comparing densities. -/
namespace Physics.LagrangianModelLiterature
set_option autoImplicit false
noncomputable section
open Math Math.LocalPolynomial.Expr Math.PairedWeylKinetic Math.ScalarWeylYukawa
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

namespace DHM
/-- Paper components in the epsilon-related basis (psi_1,-psi_0). -/
def chi (c : Bool) (a : Fin 2) : E := if a=0 then spinor c 1 else -spinor c 0
/-- epsilon^{12}=1, as in DHM (2.21)--(2.22). -/
def raised (c : Bool) (a : Fin 2) : E := if a=0 then chi c 1 else -chi c 0
def undotted : E := raised false 0*chi false 0+raised false 1*chi false 1
def dotted : E := chi true 0*raised true 0+chi true 1*raised true 1

/-- Component expansion of bar-sigma=(1,-sigma_1,-sigma_2,-sigma_3). -/
def kinetic : E :=
  chi true 0*derivative 0 (chi false 0)+chi true 1*derivative 0 (chi false 1)-
  chi true 0*derivative 1 (chi false 1)-chi true 1*derivative 1 (chi false 0)+
  Complex.I • (chi true 0*derivative 2 (chi false 1))-
  Complex.I • (chi true 1*derivative 2 (chi false 0))-
  chi true 0*derivative 3 (chi false 0)+chi true 1*derivative 3 (chi false 1)

theorem undotted_dictionary : undotted.eval = -(2:ℂ) • (pair false).eval := by
  have ht : psi false 1*psi false 0 = -(psi false 0*psi false 1) := by
    simpa [psi] using MixedJetParity.odd_slide ((false,1),0) (psi false 0)
  simp only [undotted,raised,chi,ite_true,show (1:Fin 2) ≠ 0 from by decide,ite_false,
    eval_add,eval_mul,eval_neg,neg_neg,neg_mul,mul_neg,spinor,fermion]
  change -(psi false 0*psi false 1)+psi false 1*psi false 0 = _
  rw [ht]
  simp [pair,spinor,fermion,Math.LocalPolynomial.Expr.eval,wordIndex,two_smul,psi]

theorem dotted_dictionary : dotted.eval = (2:ℂ) • (pair true).eval := by
  have ht : psi true 1*psi true 0 = -(psi true 0*psi true 1) := by
    simpa [psi] using MixedJetParity.odd_slide ((true,1),0) (psi true 0)
  simp only [dotted,raised,chi,ite_true,show (1:Fin 2) ≠ 0 from by decide,ite_false,
    eval_add,eval_mul,eval_neg,neg_neg,neg_mul,mul_neg,spinor,fermion]
  change -(psi true 1*psi true 0)+psi true 0*psi true 1 = _
  rw [ht,neg_neg]
  simp [pair,spinor,fermion,Math.LocalPolynomial.Expr.eval,wordIndex,two_smul,psi]

theorem kinetic_dictionary : kinetic.eval = PairedWeylKinetic.density.eval := by
  simp only [kinetic,chi,ite_true,show (1:Fin 2) ≠ 0 from by decide,ite_false,
    eval_add,eval_sub,eval_mul,eval_smul,eval_derivative,eval_neg,map_neg,neg_neg,neg_mul,mul_neg,
    PairedWeylKinetic.density,YukawaModel.kineticTerm_eval]
  have hs (c : Bool) (a : Fin 2) : (spinor c a).eval = psi c a := rfl
  simp only [hs]
  dsimp only [PairedWeylKinetic.D]
  module

def paperDensity (massSquared : ℂ) (m y : ℂ) : E :=
  scalarKinetic-(massSquared/2) • phi^2+Complex.I • kinetic-
  (m/2) • undotted-(star m/2) • dotted-
  (y/2) • (phi*undotted)-(star y/2) • (phi*dotted)

def parameters (z : ℂ) : Bool → ℂ := fun c => if c then star z else -z

/-- DHM (3.1.1),(3.2.1),(4.3.2), one real scalar and one neutral Weyl species,
complexified for the algebraic variation. The scalar kinetic/mass terms are
the stated constructed addition. No reality quotient is imposed. -/
theorem density_dictionary (massSquared m y : ℂ) :
    (paperDensity massSquared m y).eval =
      (density Complex.I massSquared (parameters m) (parameters y)).eval := by
  simp only [paperDensity,ScalarWeylYukawa.density,eval_add,eval_sub,eval_smul,eval_mul,
    undotted_dictionary,dotted_dictionary,kinetic_dictionary,parameters,Bool.false_eq_true,ite_true,ite_false,
    mul_neg,mul_smul_comm,smul_smul,neg_smul,smul_neg]
  module

theorem undotted_euler : undotted.euler = (-2:ℂ) • (pair false).euler := by
  classical
  apply Finsupp.ext
  intro s
  cases s with
  | inl j =>
    obtain ⟨c,a⟩ := j
    cases c <;> fin_cases a <;>
      simp [undotted,raised,chi,pair,spinor,fermion,Math.LocalPolynomial.Expr.euler,
        Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
        Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,two_smul,TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def]
  | inr j =>
    simp [undotted,raised,chi,pair,spinor,fermion,Math.LocalPolynomial.Expr.euler,
      Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
      Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def]

theorem dotted_euler : dotted.euler = (2:ℂ) • (pair true).euler := by
  classical
  apply Finsupp.ext
  intro s
  cases s with
  | inl j =>
    obtain ⟨c,a⟩ := j
    cases c <;> fin_cases a <;>
      simp [dotted,raised,chi,pair,spinor,fermion,Math.LocalPolynomial.Expr.euler,
        Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
        Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,two_smul,TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def]
  | inr j =>
    simp [dotted,raised,chi,pair,spinor,fermion,Math.LocalPolynomial.Expr.euler,
      Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
      Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def]

theorem undotted_interaction_euler : (phi*undotted).euler = (-2:ℂ) • (phi*pair false).euler := by
  classical
  have ht : MixedJetAlgebra.odd (F := Label) (B := Label) ((false,1), (0 : Fin 4 →₀ ℕ))*
      MixedJetAlgebra.odd ((false,0),0) =
      -(MixedJetAlgebra.odd ((false,0),0)*MixedJetAlgebra.odd ((false,1),0)) := by
    simpa only [MixedJetParity.involute_odd,neg_mul] using MixedJetParity.odd_slide ((false,1), (0 : Fin 4 →₀ ℕ))
      (MixedJetAlgebra.odd (F := Label) (B := Label) ((false,0),0))
  apply Finsupp.ext
  intro s
  cases s with
  | inl j =>
    obtain ⟨c,a⟩ := j
    cases c <;> fin_cases a <;>
      simp [undotted,raised,chi,phi,pair,spinor,fermion,boson,Math.LocalPolynomial.Expr.euler,
        Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
        Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,two_smul,
        TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def,scalarLabel,wordIndex,ht]
  | inr j =>
    obtain ⟨c,a⟩ := j
    cases c <;> fin_cases a <;>
      simp [undotted,raised,chi,phi,pair,spinor,fermion,boson,Math.LocalPolynomial.Expr.euler,
        Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
        Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,two_smul,
        TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def,scalarLabel,wordIndex,ht]

theorem dotted_interaction_euler : (phi*dotted).euler = (2:ℂ) • (phi*pair true).euler := by
  classical
  have ht : MixedJetAlgebra.odd (F := Label) (B := Label) ((true,1), (0 : Fin 4 →₀ ℕ))*
      MixedJetAlgebra.odd ((true,0),0) =
      -(MixedJetAlgebra.odd ((true,0),0)*MixedJetAlgebra.odd ((true,1),0)) := by
    simpa only [MixedJetParity.involute_odd,neg_mul] using MixedJetParity.odd_slide ((true,1), (0 : Fin 4 →₀ ℕ))
      (MixedJetAlgebra.odd (F := Label) (B := Label) ((true,0),0))
  apply Finsupp.ext
  intro s
  cases s with
  | inl j =>
    obtain ⟨c,a⟩ := j
    cases c <;> fin_cases a <;>
      simp [dotted,raised,chi,phi,pair,spinor,fermion,boson,Math.LocalPolynomial.Expr.euler,
        Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
        Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,two_smul,
        TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def,scalarLabel,wordIndex,ht]
  | inr j =>
    obtain ⟨c,a⟩ := j
    cases c <;> fin_cases a <;>
      simp [dotted,raised,chi,phi,pair,spinor,fermion,boson,Math.LocalPolynomial.Expr.euler,
        Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
        Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,two_smul,
        TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def,scalarLabel,wordIndex,ht]

theorem kinetic_euler_dictionary : kinetic.euler = PairedWeylKinetic.density.euler := by
  classical
  apply Finsupp.ext
  intro s
  cases s with
  | inl j =>
    rw [PairedWeylKinetic.generated_odd]
    obtain ⟨c,a⟩ := j
    cases c <;> fin_cases a <;>
      simp only [kinetic,euler_add,euler_sub,euler_smul,Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply] <;>
      simp [chi,derivative,spinor,fermion,Math.LocalPolynomial.Expr.euler,
        Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
        Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint,
        TensorProduct.neg_tmul,← Algebra.TensorProduct.one_def,wordIndex,seed,left,right,psi,
        LocalPolynomial.D,MixedJetAlgebra.totalDerivative_odd,ScalarJetAlgebra.shift] <;> abel
  | inr j =>
    rw [PairedWeylKinetic.generated_even]
    simp only [kinetic,euler_add,euler_sub,euler_smul,Finsupp.add_apply,Finsupp.sub_apply,Finsupp.smul_apply]
    simp [chi,derivative,spinor,fermion,Math.LocalPolynomial.Expr.euler,
      Math.LocalPolynomial.linearize,Math.LocalPolynomial.eulerTerms,Math.LocalPolynomial.Expr.eval,
      Math.LocalPolynomial.twist,Math.VariationalIBP.adjoint]

theorem euler_dictionary (massSquared m y : ℂ) :
    (paperDensity massSquared m y).euler =
      (density Complex.I massSquared (parameters m) (parameters y)).euler := by
  simp only [paperDensity,ScalarWeylYukawa.density,euler_add,euler_sub,euler_smul,
    undotted_euler,dotted_euler,undotted_interaction_euler,dotted_interaction_euler,
    kinetic_euler_dictionary,parameters,Bool.false_eq_true,ite_true,ite_false,smul_smul]
  module

theorem full_relation_dictionary (massSquared m y : ℂ) :
    (paperDensity massSquared m y).relations =
      (density Complex.I massSquared (parameters m) (parameters y)).relations := by
  unfold Math.LocalPolynomial.Expr.relations Math.LocalPolynomial.Expr.seeds
  rw [euler_dictionary]

def model (massSquared m y : ℂ) :=
  YukawaModel.model Complex.I massSquared (parameters m) (parameters y)

/-- Directly compile the paper's component syntax with checked symmetry. -/
def paperModel (massSquared m y : ℂ) : LagrangianModel.Mixed Label Label (Fin 4) YukawaModel.Group where
  density := paperDensity massSquared m y
  action := PairedWeylInput.action
  stable g := by
    rw [full_relation_dictionary]
    exact (model massSquared m y).stable g

def paperCoefficientEquiv (massSquared m y : ℂ) :
    (paperModel massSquared m y).input.Coefficient ≃ₗ[ℂ] (model massSquared m y).input.Coefficient :=
  LinearEquiv.ofEq
    (JetInputAdapter.Input PairedWeylInput.action (Representation.trivial ℂ YukawaModel.Group ℂ)
      (paperDensity massSquared m y).relations)
    (JetInputAdapter.Input PairedWeylInput.action (Representation.trivial ℂ YukawaModel.Group ℂ)
      (density Complex.I massSquared (parameters m) (parameters y)).relations)
    (congrArg (JetInputAdapter.Input PairedWeylInput.action (Representation.trivial ℂ YukawaModel.Group ℂ))
      (full_relation_dictionary massSquared m y))

theorem paper_evaluation (massSquared m y : ℂ)
    (f : (paperModel massSquared m y).input.Coefficient) (u : A) :
    (paperCoefficientEquiv massSquared m y f).val u = f.val u := rfl

theorem full_lorentz (massSquared m y : ℂ) (g : YukawaModel.Group) :
    PairedWeylInput.action g (paperDensity massSquared m y).eval =
      (paperDensity massSquared m y).eval := by
  rw [density_dictionary,YukawaModel.density_invariant]

theorem coefficient_equations (massSquared m y : ℂ) (q : (model massSquared m y).Coordinates) :
    ∀ j : Label, (model massSquared m y).evaluate q
      (oddEquation Complex.I (parameters m) (parameters y) j) = 0 :=
  YukawaModel.odd_coefficient_equation _ _ _ _ ((model massSquared m y).equivalence.symm q)
theorem direct_paper_equations (massSquared m y : ℂ)
    (q : (paperModel massSquared m y).Coordinates) :
    ∀ j : Label, (paperModel massSquared m y).evaluate q
      (oddEquation Complex.I (parameters m) (parameters y) j) = 0 :=
  YukawaModel.odd_coefficient_equation _ _ _ _ (paperCoefficientEquiv massSquared m y
    ((paperModel massSquared m y).equivalence.symm q))

end DHM

namespace Warsaw
theorem gaugeless_higgs (m2 lambda : ℝ) (q : (RegisteredLagrangianModels.higgs (-(m2:ℂ)) (lambda:ℂ)).Coordinates) :
    (RegisteredLagrangianModels.higgs (-(m2:ℂ)) (lambda:ℂ)).evaluate q DerivativeLiteratureHiggs.redundant =
      (1/2:ℂ)*(RegisteredLagrangianModels.higgs (-(m2:ℂ)) (lambda:ℂ)).evaluate q DerivativeLiteratureHiggs.qBox-
      (m2:ℂ)*(RegisteredLagrangianModels.higgs (-(m2:ℂ)) (lambda:ℂ)).evaluate q (DerivativeLiteratureHiggs.rho^2)+
      (lambda:ℂ)*(RegisteredLagrangianModels.higgs (-(m2:ℂ)) (lambda:ℂ)).evaluate q (DerivativeLiteratureHiggs.rho^3) := by
  simpa only [neg_mul,sub_eq_add_neg] using RegisteredLagrangianModels.higgs_relation (-(m2:ℂ)) (lambda:ℂ) q
end Warsaw

namespace CPV
theorem first_order (g : ℂ) (q : (RegisteredLagrangianModels.quartic g).Coordinates) :
    (RegisteredLagrangianModels.quartic g).evaluate q
      ((DerivativeLiteratureScalar.T (DerivativeLiteratureScalar.quarticDensity g).scalarEval).coeff 1) = 0 :=
  DerivativeLiteratureRecheck.C6.generated_first_zero g
    ((RegisteredLagrangianModels.quartic g).equivalence.symm q)

theorem higher_order_survives :
    (DerivativeLiteratureScalar.T (ScalarFirstVariation.lagrangian 0)).coeff 2 ≠ 0 :=
  DerivativeLiteratureRecheck.C6.second_order_control.2
end CPV

end
end Physics.LagrangianModelLiterature
