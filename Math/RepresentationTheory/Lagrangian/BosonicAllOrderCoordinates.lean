import Math.RepresentationTheory.Lagrangian.InteractingLagrangianCoordinates
import Math.RepresentationTheory.Lagrangian.BosonicLagrangianInput
import Mathlib.RingTheory.MvPolynomial.Basic

/-! The all-order classifier on the existing commutative generated input. -/
namespace Math.LocalPolynomial.Expr
set_option autoImplicit false
noncomputable section
variable {B I : Type*}
@[reducible] local instance : AddCommGroup (Scalar B I) := inferInstance
@[reducible] local instance : Module ℂ (Scalar B I) := inferInstance
@[reducible] local instance : Ring (Scalar B I) := inferInstance

theorem scalar_basis_span (p : Expr Empty B I) :
    Submodule.span ℂ (Set.range (DifferentialBasisRows.relation
      (fun i => (ScalarJetAlgebra.totalDerivative (S := B) i).toLinearMap)
      (MvPolynomial.basisMonomials _ ℂ) p.scalarEuler)) =
    DifferentialEquation.combined ScalarJetAlgebra.totalDerivative p.scalarSeeds := by
  have hleib : ∀ (i : I) (u v : Scalar B I),
      (ScalarJetAlgebra.totalDerivative i).toLinearMap (u*v) =
        (ScalarJetAlgebra.totalDerivative i).toLinearMap u*v+
        u*(ScalarJetAlgebra.totalDerivative i).toLinearMap v := by
    intro i u v
    change ScalarJetAlgebra.totalDerivative i (u*v) =
      ScalarJetAlgebra.totalDerivative i u*v+u*ScalarJetAlgebra.totalDerivative i v
    rw [ScalarJetAlgebra.totalDerivative_mul]
    ring
  exact (DifferentialBasisRows.span_eq
    (fun i => (ScalarJetAlgebra.totalDerivative (S := B) i).toLinearMap)
    (MvPolynomial.basisMonomials _ ℂ) p.scalarEuler
    hleib).trans
    (TwoSidedDifferential.commutative_combined ScalarJetAlgebra.totalDerivative p.scalarSeeds)

variable {B I H : Type*} [Group H]
  (p : Expr Empty B I) (rho : Representation ℂ H (Scalar B I))
  (stable : ∀ h, DifferentialEquation.combined ScalarJetAlgebra.totalDerivative p.scalarSeeds ≤
    (DifferentialEquation.combined ScalarJetAlgebra.totalDerivative p.scalarSeeds).comap (rho h))

abbrev ScalarMonomial (B I : Type*) := ScalarJetAlgebra.Index B I →₀ ℕ

def scalarAllOrderPresentation : AllOrderDerivativeCoordinates.Presentation
    (ι := ScalarMonomial B I) (κ := DifferentialBasisRows.Row I (ScalarMonomial B I) B)
    (p.scalarInput rho stable) where
  basis := MvPolynomial.basisMonomials _ ℂ
  relation := DifferentialBasisRows.relation (fun i => (ScalarJetAlgebra.totalDerivative i).toLinearMap)
    (MvPolynomial.basisMonomials _ ℂ) p.scalarEuler
  relation_span := scalar_basis_span p

def scalarAllOrderEquivalence : (p.scalarInput rho stable).Coefficient ≃ₗ[ℂ]
    (p.scalarAllOrderPresentation rho stable).rows :=
  (p.scalarAllOrderPresentation rho stable).equivalence

theorem scalarAllOrder_reconstruction (f : (p.scalarInput rho stable).Coefficient) (u : Scalar B I) :
    f.val u = ((MvPolynomial.basisMonomials (ScalarJetAlgebra.Index B I) ℂ).repr u).sum
      (fun i a => a*(p.scalarAllOrderEquivalence rho stable f).val i) :=
  (p.scalarAllOrderPresentation rho stable).reconstruction f u

def scalarTrivialAllOrderEquivalence :=
  p.scalarAllOrderEquivalence (Representation.trivial ℂ Unit _) (fun _ => le_refl _)

end
end Math.LocalPolynomial.Expr
