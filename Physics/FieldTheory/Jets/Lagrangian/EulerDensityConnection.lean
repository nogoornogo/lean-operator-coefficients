import Math.RepresentationTheory.Lagrangian.StandardDensityAction
import Physics.FieldTheory.Jets.Lagrangian.YukawaDensitySymmetry
import Physics.FieldTheory.Jets.Lagrangian.LagrangianModelLiterature
import Physics.FieldTheory.Jets.Lagrangian.YukawaModelControls

/-! Independent density-to-Euler verification for the full scalar/Weyl model.
The constructor uses density invariance, not the pre-existing Euler certificate. -/
namespace Physics.EulerDensityConnection
set_option autoImplicit false
noncomputable section
open Math Math.LocalPolynomial Math.PairedWeylKinetic Math.ScalarWeylYukawa
abbrev Group := LorentzDirections.Group
@[reducible] local instance densityAdd : AddCommGroup A := inferInstance
@[reducible] local instance densityModule : Module ℂ A := inferInstance
@[reducible] local instance densityRing : Ring A := inferInstance

def automaticModel (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :
    LagrangianModel.Mixed Label Label (Fin 4) Group :=
  StandardDensityAction.model PairedWeylInput.fields
    (Representation.trivial ℂ Group (JetLinear.Field Label)) LorentzDirections.direction
    (density kappa massSquared mass yukawa)
    (YukawaModel.density_invariant kappa massSquared mass yukawa)

/-- The automatically generated input is the same as the independently checked model. -/
theorem model_eq (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :
    automaticModel kappa massSquared mass yukawa =
      YukawaModel.model kappa massSquared mass yukawa := rfl

theorem automatic_euler (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) (g : Group) :
    (density kappa massSquared mass yukawa).euler =
      CoefficientTransport.push
        (StandardDensityAction.fieldAction PairedWeylInput.fields
          (Representation.trivial ℂ Group (JetLinear.Field Label)) g)
        (PairedWeylInput.action g) (density kappa massSquared mass yukawa).euler :=
  (StandardDensityAction.prolongation PairedWeylInput.fields
    (Representation.trivial ℂ Group (JetLinear.Field Label)) LorentzDirections.direction g).invariant_euler _ (YukawaModel.density_invariant kappa massSquared mass yukawa g)

/-- Semantic descent reproduces the direct primary-source syntax comparison. -/
theorem paper_euler (massSquared m y : ℂ) :
    (LagrangianModelLiterature.DHM.paperDensity massSquared m y).euler =
      (density Complex.I massSquared (LagrangianModelLiterature.DHM.parameters m)
        (LagrangianModelLiterature.DHM.parameters y)).euler := by
  apply Expr.euler_eq_of_eval_eq
  exact LagrangianModelLiterature.DHM.density_dictionary massSquared m y

/-- The input gate rejects the independently checked symmetry-breaking term. -/
theorem broken_density_rejected : ¬ ∀ g : Group,
    PairedWeylInput.action g YukawaModelControls.nonScalar = YukawaModelControls.nonScalar := by
  intro h
  exact YukawaModelControls.symmetry_breaking_control (h YukawaModelControls.boost)

end
end Physics.EulerDensityConnection
