import Math.RepresentationTheory.Lagrangian.BosonicAllOrderCoordinates
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureRecheck
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarConstantCoefficients

/-! Source-specific validation of the all-order presentation. Paper formulas
are checked under the stated scalar/Higgs and Grassmann component dictionaries. -/
namespace Physics.InteractingLagrangianLiterature
set_option autoImplicit false
noncomputable section
open Math Math.LocalPolynomial

namespace Higgs
def presentation (m2 lambda : ℝ) :=
  (Math.HiggsLagrangianInput.density (-(m2:ℂ)) (lambda:ℂ)).scalarAllOrderPresentation
    HiggsStandardInput.action (HiggsStandardInput.generated_stable _ _)

def equivalence (m2 lambda : ℝ) : (DerivativeLiteratureRecheck.C3.input m2 lambda).Coefficient ≃ₗ[ℂ]
    (presentation m2 lambda).rows := (presentation m2 lambda).equivalence

/-- Grzadkowski et al. (5.3), with the previously proved gaugeless conventions. -/
theorem paper_relation (m2 lambda : ℝ) (c : (presentation m2 lambda).rows) :
    ((equivalence m2 lambda).symm c).val DerivativeLiteratureHiggs.redundant =
      (1/2:ℂ)*((equivalence m2 lambda).symm c).val DerivativeLiteratureHiggs.qBox-
      (m2:ℂ)*((equivalence m2 lambda).symm c).val (DerivativeLiteratureHiggs.rho^2)+
      (lambda:ℂ)*((equivalence m2 lambda).symm c).val (DerivativeLiteratureHiggs.rho^3) :=
  DerivativeLiteratureRecheck.C3.coefficient_relation m2 lambda _

theorem complete_roundtrip (m2 lambda : ℝ)
    (f : (DerivativeLiteratureRecheck.C3.input m2 lambda).Coefficient) :
    (equivalence m2 lambda).symm (equivalence m2 lambda f) = f :=
  (equivalence m2 lambda).symm_apply_apply f
end Higgs

namespace Scalar
open DerivativeLiteratureScalar PolynomialScalarEOM

def presentation (g : ℂ) := (quarticDensity g).scalarAllOrderPresentation
  (quarticInput g).action (quarticInput g).stable
def equivalence (g : ℂ) : (quarticInput g).Coefficient ≃ₗ[ℂ] (presentation g).rows :=
  (presentation g).equivalence

/-- The constructed interacting specialization of Criado--Perez-Victoria (3.2). -/
theorem first_order_on_shell (g : ℂ) (c : (presentation g).rows) :
    ((equivalence g).symm c).val
      ((T (quarticDensity g).scalarEval).coeff 1) = 0 :=
  DerivativeLiteratureRecheck.C6.generated_first_zero g _

theorem cubic_value_iff (g c : ℂ) :
    (∃ q : (presentation g).rows, ((equivalence g).symm q).val (field^3) = c) ↔ g*c=0 := by
  constructor
  · rintro ⟨q,hq⟩
    exact (ScalarConstantCoefficients.cubic_value_iff g c).mp
      ⟨toDirect g ((equivalence g).symm q),hq⟩
  · intro h
    obtain ⟨f,hf⟩ := (ScalarConstantCoefficients.cubic_value_iff g c).mpr h
    refine ⟨equivalence g (toHelper g f),?_⟩
    rw [(equivalence g).symm_apply_apply]
    exact hf

theorem higher_order_not_erased :
    (T (ScalarFirstVariation.lagrangian 0)).coeff 2 ≠ 0 :=
  DerivativeLiteratureRecheck.C6.second_order_control.2
end Scalar

namespace TongYukawa
open Expr
abbrev Label := Bool × Fin 4
abbrev E := Expr Label Unit (Fin 4)
abbrev A := LocalPolynomial.A Label Unit (Fin 4)
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def phi : E := boson ()
def spinor (barred : Bool) (i : Fin 4) : E := fermion (barred,i)
def pair (i : Fin 4) : E := spinor false i * spinor true i
def bilinear : E := pair 0+pair 1+pair 2+pair 3
def density (g : ℂ) : E := -g • (phi*bilinear)

/-- Literal interaction part of Tong (5.475); barred components are independent. -/
theorem density_eval (g : ℂ) : (density g).eval = -g •
    (phi.eval * ((spinor false 0).eval*(spinor true 0).eval+
      (spinor false 1).eval*(spinor true 1).eval+
      (spinor false 2).eval*(spinor true 2).eval+
      (spinor false 3).eval*(spinor true 3).eval)) := by
  simp only [density,eval_smul,eval_mul,bilinear,eval_add,pair]

theorem scalar_euler (g : ℂ) : (density g).euler (.inr ()) = -g • bilinear.eval := by
  simp [density,phi,bilinear,pair,spinor,fermion,boson,Expr.smul_def,euler,linearize,eulerTerms,
    eval,twist,VariationalIBP.adjoint,Algebra.smul_def]

theorem barred_euler (g : ℂ) (i : Fin 4) :
    (density g).euler (.inl (false,i)) = -g • (phi.eval*(spinor true i).eval) := by
  fin_cases i <;> simp [density,phi,bilinear,pair,spinor,fermion,boson,Expr.smul_def,euler,linearize,eulerTerms,
    eval,twist,VariationalIBP.adjoint,Algebra.smul_def]

theorem unbarred_euler (g : ℂ) (i : Fin 4) :
    (density g).euler (.inl (true,i)) = g • (phi.eval*(spinor false i).eval) := by
  fin_cases i <;> simp [density,phi,bilinear,pair,spinor,fermion,boson,Expr.smul_def,euler,linearize,eulerTerms,
    eval,twist,VariationalIBP.adjoint,Algebra.smul_def,
    TensorProduct.neg_tmul,neg_mul]

def input (g : ℂ) := (density g).trivialInput
def presentation (g : ℂ) := (density g).allOrderPresentation (Representation.trivial ℂ Unit _)
  (fun _ => le_refl _)
def equivalence (g : ℂ) : (input g).Coefficient ≃ₗ[ℂ] (presentation g).rows :=
  (presentation g).equivalence

theorem complete_roundtrip (g : ℂ) (f : (input g).Coefficient) :
    (equivalence g).symm (equivalence g f) = f := (equivalence g).symm_apply_apply f
end TongYukawa

end
end Physics.InteractingLagrangianLiterature
