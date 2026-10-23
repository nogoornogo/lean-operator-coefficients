import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarDerivativeInterface
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarFirstVariation
import Physics.FieldTheory.Jets.Lagrangian.LagrangianHelper

/-! Actual scalar input comparisons with the low-degree sector of
1706.08520v1 and the polynomial specialization of 1811.09413v2.
Invariant completeness is not assumed by these relation certificates. -/
namespace Physics.DerivativeLiteratureScalar
set_option autoImplicit false
noncomputable section
open Math MvPolynomial PolynomialScalarEOM

def twoDerivative : OffShell := field^2 * LorentzJetIBP.kinetic
def fourDerivative : OffShell := LorentzJetIBP.kinetic^2
abbrev freeInput := ScalarDerivativeInterface.scalar 0

theorem four_invariant (a : LorentzDirections.Group) :
    offAction a fourDerivative = fourDerivative := by
  rw [fourDerivative, map_pow]
  exact congrArg (fun p : OffShell => p^2) (LorentzJetIBP.kinetic_invariant a)

theorem two_variation : ScalarFirstVariation.delta (field^3)
    (ScalarFirstVariation.lagrangian 0) = (3 : ℂ) • twoDerivative := by
  have hv : ScalarFirstVariation.delta (field^3) LorentzJetIBP.kinetic =
      (6 : ℂ) • twoDerivative := by
    simp [LorentzJetIBP.kinetic_formula, twoDerivative,
      ScalarFirstVariation.delta_first,
      ScalarJetAlgebra.totalDerivative_X, ScalarJetAlgebra.shift,
      field, MasslessScalarEOM.field, Algebra.smul_def, MvPolynomial.algebraMap_eq]
    norm_num only [map_ofNat]
    ring
  simp only [ScalarFirstVariation.lagrangian, zero_div, zero_smul, sub_zero]
  calc
    _ = (1/2 : ℂ) • ScalarFirstVariation.delta (field^3) LorentzJetIBP.kinetic :=
      (ScalarFirstVariation.delta (field^3)).toLinearMap.map_smul _ _
    _ = _ := by rw [hv, smul_smul]; norm_num

theorem two_projection_zero : freeInput.projection twoDerivative = 0 := by
  change integrated 0 twoDerivative = 0
  have h := ScalarFirstVariation.first_variation_onShell 0 (field^3)
  rw [two_variation, map_smul] at h
  have hc := congrArg (fun p => (1/3 : ℂ) • p) h
  simpa only [smul_smul, show (1/3 : ℂ)*3 = 1 by norm_num,
    one_smul, smul_zero] using hc

theorem two_coefficient_zero (f : freeInput.Coefficient) : f.val twoDerivative = 0 := by
  rw [← freeInput.extraction f twoDerivative, two_projection_zero, map_zero]

theorem four_extraction (f : freeInput.Coefficient) :
    freeInput.coefficientEquiv f (freeInput.projection fourDerivative) = f.val fourDerivative := rfl

open LocalPolynomial LocalPolynomial.Expr
def quarticPotential (g : ℂ) : ScalarLagrangianHelper.E := (-g/4) • ScalarLagrangianHelper.phi^4
def quarticDensity (g : ℂ) : ScalarLagrangianHelper.E := ScalarLagrangianHelper.kinetic+quarticPotential g

theorem quartic_eval (g : ℂ) : (quarticDensity g).scalarEval = ScalarFirstVariation.lagrangian g := by
  have hp : ScalarLagrangianHelper.phi.scalarEval = field := by
    simp only [ScalarLagrangianHelper.phi,Expr.boson,Expr.scalarEval,
      Expr.eval,wordIndex,scalarProjection_even]
    rfl
  have hk := ScalarLagrangianHelper.density_eval 0
  simp only [ScalarLagrangianHelper.density, LagrangianControls.potential,
    zero_div, neg_zero, zero_smul,scalarEval_add,scalarEval_smul,add_zero] at hk
  simp only [quarticDensity,quarticPotential,scalarEval_add,scalarEval_smul,scalarEval_pow,hp,hk]
  simp [ScalarFirstVariation.lagrangian,neg_div,neg_smul,sub_eq_add_neg]

theorem quartic_potential_euler (g : ℂ) :
    (quarticPotential g).scalarEuler () = -g • field^3 := by
  have hc : (MvPolynomial.C (-1/4 : ℂ) : OffShell)*4 = -1 := by
    have he : (-1/4 : ℂ)*4 = -1 := by norm_num
    simpa only [map_mul,map_ofNat,map_neg,map_one] using congrArg (fun c => (MvPolynomial.C c : OffShell)) he
  simp [quarticPotential,ScalarLagrangianHelper.phi,Expr.boson,Expr.smul_def,
    Expr.scalarEuler,Expr.euler,linearize,eulerTerms,Expr.eval,twist,
    VariationalIBP.adjoint,wordIndex,scalarProjection_even,map_mul,map_add]
  have hcoef : (MvPolynomial.C (-g/4) : OffShell) = C g*C (-1/4:ℂ) := by
    rw [← map_mul]; congr 1; ring
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq,hcoef]
  simp only [field,MasslessScalarEOM.field] at *
  linear_combination (C g*X ((),0)^3)*hc

theorem quartic_euler (g : ℂ) : (quarticDensity g).scalarEuler () = -seed g := by
  rw [quarticDensity,scalarEuler_add,ScalarLagrangianHelper.kinetic_euler,quartic_potential_euler]
  simp only [seed,neg_add,MvPolynomial.smul_eq_C_mul,neg_smul]

theorem quartic_seeds (g : ℂ) : (quarticDensity g).scalarSeeds = {ScalarFirstVariation.eulerEquation g} := by
  ext p
  constructor
  · rintro ⟨b,rfl⟩
    cases b
    exact Set.mem_singleton_iff.mpr (quartic_euler g)
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    exact ⟨(),(quartic_euler g).trans hp.symm⟩

theorem quartic_ideal (g : ℂ) :
    DifferentialEquation.ideal PolynomialScalarEOM.D (quarticDensity g).scalarSeeds = ideal g := by
  rw [quartic_seeds]
  exact ScalarFirstVariation.euler_ideal_eq g

theorem quartic_relations (g : ℂ) :
    DifferentialEquation.combined PolynomialScalarEOM.D (quarticDensity g).scalarSeeds =
      DifferentialEquation.combined PolynomialScalarEOM.D (equations g) := by
  unfold DifferentialEquation.combined DifferentialEquation.relations
  rw [quartic_ideal]

def quarticInput (g : ℂ) := (quarticDensity g).scalarInput ScalarInputAdapter.lorentzAction (by
  change ∀ a, DifferentialEquation.combined PolynomialScalarEOM.D (quarticDensity g).scalarSeeds ≤ _
  rw [quartic_relations]
  exact ScalarInputAdapter.lorentz_stable g)

def toDirect (g : ℂ) (f : (quarticInput g).Coefficient) :
    (ScalarDerivativeInterface.scalar g).Coefficient := ⟨f.val, by
  intro p hp
  apply f.property
  change p ∈ DifferentialEquation.combined PolynomialScalarEOM.D (quarticDensity g).scalarSeeds
  rw [quartic_relations]
  exact hp⟩

def toHelper (g : ℂ) (f : (ScalarDerivativeInterface.scalar g).Coefficient) :
    (quarticInput g).Coefficient := ⟨f.val, by
  intro p hp
  apply f.property
  change p ∈ DifferentialEquation.combined PolynomialScalarEOM.D (equations g)
  rw [← quartic_relations]
  exact hp⟩

theorem direct_helper_inverse (g : ℂ) (f : (ScalarDerivativeInterface.scalar g).Coefficient) :
    toDirect g (toHelper g f) = f := Subtype.ext rfl

theorem helper_direct_inverse (g : ℂ) (f : (quarticInput g).Coefficient) :
    toHelper g (toDirect g f) = f := Subtype.ext rfl

theorem extraction_agrees (g : ℂ) (f : (quarticInput g).Coefficient) (p : OffShell) :
    (quarticInput g).coefficientEquiv f ((quarticInput g).projection p) =
    (ScalarDerivativeInterface.scalar g).coefficientEquiv (toDirect g f)
      ((ScalarDerivativeInterface.scalar g).projection p) := rfl

theorem substitution_zero (g : ℂ) :
    (JetFirstVariation.substitution (fun _ : Unit => field^3)
      (quarticDensity g).scalarEval).coeff 0 = ScalarFirstVariation.lagrangian g := by
  rw [JetFirstVariation.substitution_zero,quartic_eval]

theorem substitution_first (g : ℂ) :
    (JetFirstVariation.substitution (fun _ : Unit => field^3)
      (quarticDensity g).scalarEval).coeff 1 =
      -(field^3)*seed g+∑ i, PolynomialScalarEOM.D i (ScalarFirstVariation.current (field^3) i) := by
  rw [quartic_eval]
  exact ScalarFirstVariation.substitution_first g _

abbrev T := JetFirstVariation.substitution (fun _ : Unit => field^3)

theorem substitution_first_jet (i : Fin 4) :
    T (PolynomialScalarEOM.D i field) = Polynomial.C (PolynomialScalarEOM.D i field)+
      Polynomial.C (3*field^2*PolynomialScalarEOM.D i field)*Polynomial.X := by
  have hv : JetFirstVariation.variation (fun _ : Unit => field^3)
      (X ((),Finsupp.single i 1)) = 3*field^2*PolynomialScalarEOM.D i field := by
    rw [show JetFirstVariation.variation (fun _ : Unit => field^3)
      (X ((),Finsupp.single i 1)) = PolynomialScalarEOM.D i (field^3) from
        ScalarFirstVariation.delta_first _ i]
    simp
    ring
  have hj : PolynomialScalarEOM.D i field = X ((),Finsupp.single i 1) := by
    simp [field,MasslessScalarEOM.field,ScalarJetAlgebra.totalDerivative_X,ScalarJetAlgebra.shift]
  rw [hj,JetFirstVariation.substitution_X,← JetFirstVariation.variation_X,hv,hj]

theorem kinetic_as_derivatives : LorentzJetIBP.kinetic =
    (PolynomialScalarEOM.D 0 field)^2-(PolynomialScalarEOM.D 1 field)^2-
    (PolynomialScalarEOM.D 2 field)^2-(PolynomialScalarEOM.D 3 field)^2 := by
  simp [LorentzJetIBP.kinetic_formula,field,MasslessScalarEOM.field,
    ScalarJetAlgebra.totalDerivative_X,ScalarJetAlgebra.shift]

theorem substituted_kinetic : T LorentzJetIBP.kinetic =
    Polynomial.C LorentzJetIBP.kinetic+
    Polynomial.C (6*field^2*LorentzJetIBP.kinetic)*Polynomial.X+
    Polynomial.C (9*field^4*LorentzJetIBP.kinetic)*Polynomial.X^2 := by
  simp only [kinetic_as_derivatives,map_sub,map_pow,substitution_first_jet,map_mul]
  norm_num only [map_ofNat]
  ring

theorem substitution_second (g : ℂ) :
    (T (ScalarFirstVariation.lagrangian g)).coeff 2 =
      (9/2:ℂ) • (field^4*LorentzJetIBP.kinetic)-(3*g/2) • field^8 := by
  have hf : T field = Polynomial.C field+Polynomial.C (field^3)*Polynomial.X := by
    simpa only [T,field,MasslessScalarEOM.field,JetFirstVariation.prolong_zero] using
      JetFirstVariation.substitution_X (fun _ : Unit => field^3) ((),0)

  have ht : T (ScalarFirstVariation.lagrangian g) =
      (1/2:ℂ) • T LorentzJetIBP.kinetic-(g/4) • (T field)^4 := by
    exact (T.toLinearMap.map_sub _ _).trans (congrArg₂ (·-·)
      (T.toLinearMap.map_smul _ _) ((T.toLinearMap.map_smul _ _).trans
        (congrArg ((g/4:ℂ) • ·) (map_pow T field 4))))
  rw [ht,substituted_kinetic,hf]
  have he (x y : OffShell) : (Polynomial.C x+Polynomial.C y*Polynomial.X)^4 =
      Polynomial.C (x^4)+Polynomial.C (4*x^3*y)*Polynomial.X+
      Polynomial.C (6*x^2*y^2)*Polynomial.X^2+
      Polynomial.C (4*x*y^3)*Polynomial.X^3+Polynomial.C (y^4)*Polynomial.X^4 := by
    simp only [map_mul,map_pow]
    norm_num only [map_ofNat]
    ring
  rw [he]
  simp only [Polynomial.coeff_sub,Polynomial.coeff_smul,Polynomial.coeff_add,
    Polynomial.coeff_C,Polynomial.coeff_C_mul_X,Polynomial.coeff_C_mul_X_pow]
  norm_num
  have hk : (9:OffShell)*field^4*LorentzJetIBP.kinetic =
      (9:ℂ) • (field^4*LorentzJetIBP.kinetic) := by
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq]
    norm_num only [map_ofNat]
    ring
  have hp : (6:OffShell)*field^2*(field^3)^2 = (6:ℂ) • field^8 := by
    simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq]
    norm_num only [map_ofNat]
    ring
  rw [hk,hp]
  module

def rawProbe : OffShell →ₐ[ℂ] ℂ := aeval (fun j =>
  if j.2 = 0 ∨ j.2 = Finsupp.single 0 1 then 1 else 0)

theorem rawProbe_field : rawProbe field = 1 := by
  simp [rawProbe,field,MasslessScalarEOM.field]

theorem rawProbe_kinetic : rawProbe LorentzJetIBP.kinetic = 1 := by
  have hs (i j : Fin 4) : (Finsupp.single i (1:ℕ) : Fin 4 →₀ ℕ) =
      Finsupp.single j 1 ↔ i = j := Finsupp.single_left_inj (by decide)
  have hz (i : Fin 4) : (Finsupp.single i (1:ℕ) : Fin 4 →₀ ℕ) ≠ 0 := by
    intro h
    have he := congrArg (fun v : Fin 4 →₀ ℕ => v i) h
    simp at he
  norm_num [LorentzJetIBP.kinetic_formula,rawProbe,hs,hz]

theorem second_raw_nonzero : (T (ScalarFirstVariation.lagrangian 0)).coeff 2 ≠ 0 := by
  intro hz
  have he := congrArg rawProbe hz
  rw [substitution_second] at he
  norm_num [map_sub,map_smul,map_mul,map_pow,rawProbe_field,rawProbe_kinetic] at he

theorem helper_first_onShell (g : ℂ) :
    (quarticInput g).projection ((T (quarticDensity g).scalarEval).coeff 1) = 0 := by
  rw [JetFirstVariation.substitution_first]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change JetFirstVariation.variation (fun _ : Unit => field^3) (quarticDensity g).scalarEval ∈
    DifferentialEquation.combined PolynomialScalarEOM.D (quarticDensity g).scalarSeeds
  rw [quartic_relations,quartic_eval]
  exact (Submodule.Quotient.mk_eq_zero _).mp
    (ScalarFirstVariation.first_variation_onShell g (field^3))

end
end Physics.DerivativeLiteratureScalar
