import Math.RepresentationTheory.Lagrangian.LagrangianModel
import Physics.FieldTheory.Jets.Lagrangian.LagrangianHelper
import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsStandardInput
import Physics.FieldTheory.Jets.Scalar.Inputs.ScalarConstantCoefficients
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureScalar

/-! Model-facing factories reuse checked densities, actions and stability.
The literature namespaces are not required to construct these models. -/
namespace Physics.RegisteredLagrangianModels
set_option autoImplicit false
noncomputable section
open Math

def scalar (g : ℂ) : LagrangianModel.Bosonic Unit (Fin 4) LorentzDirections.Group :=
  ⟨ScalarLagrangianHelper.density g,ScalarInputAdapter.lorentzAction,
    ScalarLagrangianHelper.stable g⟩

def higgs (a b : ℂ) : LagrangianModel.Bosonic DerivativeLiteratureHiggs.Label (Fin 4)
    HiggsStandardInput.Group :=
  ⟨Math.HiggsLagrangianInput.density a b,HiggsStandardInput.action,
    HiggsStandardInput.generated_stable a b⟩

def quartic (g : ℂ) : LagrangianModel.Bosonic Unit (Fin 4) LorentzDirections.Group :=
  ⟨DerivativeLiteratureScalar.quarticDensity g,(DerivativeLiteratureScalar.quarticInput g).action,
    (DerivativeLiteratureScalar.quarticInput g).stable⟩

theorem scalar_input (g : ℂ) : (scalar g).input = ScalarLagrangianHelper.input g := rfl
theorem higgs_input (a b : ℂ) : (higgs a b).input = HiggsStandardInput.input a b := rfl
theorem quartic_input (g : ℂ) : (quartic g).input = DerivativeLiteratureScalar.quarticInput g := rfl

theorem higgs_relation (a b : ℂ) (q : (higgs a b).Coordinates) :
    (higgs a b).evaluate q DerivativeLiteratureHiggs.redundant =
      (1/2:ℂ)*(higgs a b).evaluate q DerivativeLiteratureHiggs.qBox+
      a*(higgs a b).evaluate q (DerivativeLiteratureHiggs.rho^2)+
      b*(higgs a b).evaluate q (DerivativeLiteratureHiggs.rho^3) :=
  HiggsStandardInput.higgs_relation a b ((higgs a b).equivalence.symm q)

theorem quartic_cubic_value_iff (g c : ℂ) :
    (∃ q : (quartic g).Coordinates,
      (quartic g).evaluate q (PolynomialScalarEOM.field^3) = c) ↔ g*c=0 := by
  constructor
  · rintro ⟨q,hq⟩
    exact (ScalarConstantCoefficients.cubic_value_iff g c).mp
      ⟨DerivativeLiteratureScalar.toDirect g ((quartic g).equivalence.symm q),hq⟩
  · intro h
    obtain ⟨f,hf⟩ := (ScalarConstantCoefficients.cubic_value_iff g c).mpr h
    refine ⟨(quartic g).equivalence (DerivativeLiteratureScalar.toHelper g f),?_⟩
    exact (LagrangianModel.Bosonic.evaluate_encode (quartic g)
      (DerivativeLiteratureScalar.toHelper g f) _).trans hf

end
end Physics.RegisteredLagrangianModels
