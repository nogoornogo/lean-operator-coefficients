import Math.RepresentationTheory.Fields.JetConnection
import Math.RepresentationTheory.Lagrangian.LagrangianModelControls
import Physics.FieldTheory.Jets.Lagrangian.EulerDensityConnection

/-! A nontrivial field-coordinate change on the complete scalar/Weyl density
input, and selection in its full quotient. The two odd blocks change sign;
the bosonic fields and the actual direction action are retained. -/
namespace Physics.LagrangianFieldInputConnection
set_option autoImplicit false
noncomputable section
open Math Representation LocalPolynomial PairedWeylKinetic ScalarWeylYukawa
abbrev Group := LorentzDirections.Group
@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def oddDictionary : Representation.Equiv PairedWeylInput.fields PairedWeylInput.fields :=
  .mk (LinearEquiv.neg ℂ) (by
    intro g
    apply LinearMap.ext
    intro v
    exact (map_neg (PairedWeylInput.fields g) v).symm)

abbrev evenFields := Representation.trivial ℂ Group (JetLinear.Field Label)

def sourceDictionary := FieldJetConnection.fieldEquiv oddDictionary
  (Representation.Equiv.refl evenFields) LorentzDirections.direction

theorem odd_generator (v : JetLinear.Field Label) (a : Fin 4 →₀ ℕ) :
    sourceDictionary (JetFunctor.oddVector (JetLinear.atOrder a v)) =
      JetFunctor.oddVector (JetLinear.atOrder a (-v)) :=
  FieldJetConnection.generator oddDictionary.toIntertwiningMap
    (IntertwiningMap.id evenFields) LorentzDirections.direction v a

def model (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :=
  EulerDensityConnection.automaticModel kappa massSquared mass yukawa

def input (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :=
  (model kappa massSquared mass yukawa).input.pullAlong sourceDictionary.toIntertwiningMap

def coefficientEquiv (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :=
  (model kappa massSquared mass yukawa).input.pullEquiv sourceDictionary

theorem evaluation (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (f : (model kappa massSquared mass yukawa).input.Coefficient) (u : A) :
    (coefficientEquiv kappa massSquared mass yukawa f).val u = f.val (sourceDictionary u) := rfl

theorem roundtrip (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (f : (model kappa massSquared mass yukawa).input.Coefficient) :
    (coefficientEquiv kappa massSquared mass yukawa).symm
      (coefficientEquiv kappa massSquared mass yukawa f) = f :=
  (coefficientEquiv kappa massSquared mass yukawa).symm_apply_apply f

theorem full_relations (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :
    (input kappa massSquared mass yukawa).relations =
      (TwoSidedDifferential.combined D
        (Set.range (YukawaModel.independentEuler kappa massSquared mass yukawa))).comap
          sourceDictionary.toLinearMap := by
  change (YukawaModel.input kappa massSquared mass yukawa).relations.comap _ = _
  rw [YukawaModel.full_relations]

def evenSector : Subrepresentation PairedWeylInput.action :=
  FieldSelection.fixed PairedWeylInput.action (fun _ : Unit => sourceDictionary.toLinearMap)
    (fun _ g u => sourceDictionary.isIntertwining _ _ g u)

def selected (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :=
  (model kappa massSquared mass yukawa).input.selectedFields evenSector
    (Representation.Equiv.refl evenSector.toRepresentation)

theorem selected_relations (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :
    (selected kappa massSquared mass yukawa).relations =
      (model kappa massSquared mass yukawa).input.relations.comap evenSector.toSubmodule.subtype := rfl

theorem selected_evaluation (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ)
    (f : (model kappa massSquared mass yukawa).input.Coefficient) (u : evenSector.toSubmodule) :
    ((model kappa massSquared mass yukawa).input.pullCoefficient (FieldSelection.inclusion evenSector) f).val u =
      f.val u.val := rfl

def selectedImageEquiv (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) :=
  (model kappa massSquared mass yukawa).input.imageEquiv (FieldSelection.inclusion evenSector)

def cancellingModel (p : E) : LagrangianModel.Mixed Label Label (Fin 4) Group :=
  StandardDensityAction.model PairedWeylInput.fields evenFields LorentzDirections.direction (p-p)
    (by intro g; simp)

theorem cancelling_relations (p : E) :
    (cancellingModel p).input.relations = (VariationalIBP.divergence D).range :=
  LagrangianModelControls.cancellation_relations p

theorem cancelling_connection (p : E) :
    ((cancellingModel p).input.pullAlong sourceDictionary.toIntertwiningMap).relations =
      ((VariationalIBP.divergence D).range).comap sourceDictionary.toLinearMap := by
  change (cancellingModel p).input.relations.comap _ = _
  rw [cancelling_relations]

theorem independent_density_covariance (kappa massSquared : ℂ) (mass yukawa : Bool → ℂ) (g : Group) :
    (density kappa massSquared mass yukawa).euler =
      CoefficientTransport.push (StandardDensityAction.fieldAction PairedWeylInput.fields evenFields g)
        (PairedWeylInput.action g) (density kappa massSquared mass yukawa).euler :=
  EulerDensityConnection.automatic_euler kappa massSquared mass yukawa g

def paperCoefficientEquiv (massSquared m y : ℂ) :=
  (LagrangianModelLiterature.DHM.paperCoefficientEquiv massSquared m y).trans
    (coefficientEquiv Complex.I massSquared
      (LagrangianModelLiterature.DHM.parameters m) (LagrangianModelLiterature.DHM.parameters y))

theorem paper_evaluation (massSquared m y : ℂ)
    (f : (LagrangianModelLiterature.DHM.paperModel massSquared m y).input.Coefficient) (u : A) :
    (paperCoefficientEquiv massSquared m y f).val u = f.val (sourceDictionary u) :=
  LagrangianModelLiterature.DHM.paper_evaluation massSquared m y f (sourceDictionary u)

end
end Physics.LagrangianFieldInputConnection
