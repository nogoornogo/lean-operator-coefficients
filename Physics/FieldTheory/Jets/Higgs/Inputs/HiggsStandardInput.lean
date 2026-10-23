import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsFieldDictionary
import Physics.FieldTheory.Jets.Higgs.Inputs.HiggsLagrangianInput
import Math.RepresentationTheory.Higgs.HiggsInternalSymmetry

/-! Generated gaugeless Higgs input with actual SM internal and Lorentz actions.
The covering SM gauge group acts globally; no gauge connection is supplied. -/
namespace Physics.HiggsStandardInput
set_option autoImplicit false
noncomputable section
open Math DerivativeLiteratureHiggs JetDirections
abbrev Group := StandardSMGaugeTensor.GaugeGroup × LorentzDirections.Group

def fields : Representation ℂ Group (JetLinear.Field Label) :=
  HiggsFieldDictionary.action.comp (MonoidHom.fst _ _)
def directions : Representation ℂ Group (Direction (Fin 4)) :=
  LorentzDirections.direction.comp (MonoidHom.snd _ _)
def jets := combined fields directions
def action := JetFunctor.polynomialAction jets
def transport (g : Group) : A →ₐ[ℂ] A := JetFunctor.polynomialMap (jets g)

theorem factorize (g : Group) (p : A) : transport g p =
    HiggsInternalSymmetry.transport HiggsFieldDictionary.higgs g.1
      (HiggsLagrangianInput.transport g.2 p) := by
  change JetFunctor.polynomialMap ((JetLinear.map (HiggsFieldDictionary.action g.1)).comp
    (jetMap (LorentzDirections.direction g.2))) p = _
  rw [JetFunctor.polynomialMap_comp]
  rfl

theorem ideal_stable (a b : ℂ) (g : Group) :
    ∀ p ∈ DifferentialEquation.ideal D (seeds a b),
      transport g p ∈ DifferentialEquation.ideal D (seeds a b) := by
  intro p hp
  rw [factorize]
  exact HiggsInternalSymmetry.ideal_stable HiggsFieldDictionary.higgs a b g.1 _
    (HiggsLagrangianInput.ideal_stable a b g.2 p hp)

theorem covariance (g : Group) (i : Fin 4) (p : A) :
    transport g (D i p) = ∑ k, (directions g (Finsupp.single i 1)) k •
      D k (transport g p) :=
  JetFunctor.polynomial_covariant jets g i _ (combined_covariant fields directions g i) p

theorem stable (a b : ℂ) : ∀ g, DifferentialEquation.combined D (seeds a b) ≤
    (DifferentialEquation.combined D (seeds a b)).comap (action g) := by
  intro g
  exact DifferentialEquation.combined_map_stable D _ (transport g) (ideal_stable a b g)
    (fun i k => (directions g (Finsupp.single i 1)) k) (covariance g)

theorem generated_stable (a b : ℂ) : ∀ g,
    DifferentialEquation.combined D (Math.HiggsLagrangianInput.density a b).scalarSeeds ≤
      (DifferentialEquation.combined D (Math.HiggsLagrangianInput.density a b).scalarSeeds).comap
        (action g) := by
  rw [Math.HiggsLagrangianInput.generated_relations]
  exact stable a b

/-- The caller supplies the potential parameters; action/stability are packaged. -/
def input (a b : ℂ) :=
  (Math.HiggsLagrangianInput.density a b).scalarInput action (generated_stable a b)
def direct (a b : ℂ) := DerivativeInterface.equations D (seeds a b) action (stable a b)

def toDirect (a b : ℂ) (f : (input a b).Coefficient) : (direct a b).Coefficient :=
  ⟨f.val,by
    intro p hp
    apply f.property
    change p ∈ DifferentialEquation.combined D (Math.HiggsLagrangianInput.density a b).scalarSeeds
    rw [Math.HiggsLagrangianInput.generated_relations]
    exact hp⟩
def toGenerated (a b : ℂ) (f : (direct a b).Coefficient) : (input a b).Coefficient :=
  ⟨f.val,by
    intro p hp
    apply f.property
    change p ∈ DifferentialEquation.combined D (seeds a b)
    rw [← Math.HiggsLagrangianInput.generated_relations]
    exact hp⟩
def coefficientEquiv (a b : ℂ) : (input a b).Coefficient ≃ₗ[ℂ] (direct a b).Coefficient where
  toFun := toDirect a b
  invFun := toGenerated a b
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extraction (a b : ℂ) (f : (input a b).Coefficient) (p : A) :
    (coefficientEquiv a b f).val p = f.val p := rfl

def forgetSymmetries (a b : ℂ) (f : (input a b).Coefficient) :
    (Math.HiggsLagrangianInput.input a b).Coefficient := ⟨{
  toLinearMap := f.val.toLinearMap
  isIntertwining' _ := rfl },f.property⟩

theorem higgs_relation (a b : ℂ) (f : (input a b).Coefficient) :
    f.val redundant = (1/2:ℂ)*f.val qBox+a*f.val (rho^2)+b*f.val (rho^3) :=
  Math.HiggsLagrangianInput.higgs_relation a b (forgetSymmetries a b f)

end
end Physics.HiggsStandardInput
