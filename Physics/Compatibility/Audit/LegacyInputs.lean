import Physics.FieldTheory.Mass.InvariantMassData
import Physics.FieldTheory.Mass.SymmetricMassIndex
import Physics.FieldTheory.Jets.ScalarInputAdapter
import Physics.FieldTheory.Jets.RegisteredLagrangianModels
import Math.RepresentationTheory.ProhibitionInput
import Math.RepresentationTheory.MixedOperatorInput

/-! Consumer checks using published routes and names. Expected deprecation
warnings identify the replacements. These are algebraic API controls. -/

noncomputable section
namespace Physics.LegacyInputControl

def mass : GUT.InvariantWeylMass.SymmetricMass (Representation.trivial ℂ Unit ℂ) where
  form := 0
  symmetric := LinearMap.BilinForm.isSymm_zero
  invariant := by intros; rfl

example : mass.form = 0 := rfl
example : mass.restrict (MonoidHom.id Unit) = mass := by ext; rfl
example (x : ℂ) : x ∈ mass.radical.toSubmodule := by
  exact (GUT.InvariantWeylMass.SymmetricMass.mem_radical mass x).mpr (by intro y; rfl)

example (m : GUT.InvariantWeylMass.SymmetricMass (Representation.trivial ℂ Unit ℂ))
    (x y : ℂ) : (match m with
      | GUT.InvariantWeylMass.SymmetricMass.mk form _ _ => form x y) = m.form x y := by
  cases m
  rfl

example : Module ℂ GUT.PolynomialScalarEOM.OffShell := inferInstance

example (g : ℂ) (f : GUT.ScalarInputAdapter.Input g) :
    f.val GUT.LorentzJetIBP.waveField + g * f.val (GUT.PolynomialScalarEOM.field ^ 3) = 0 :=
  GUT.ScalarInputAdapter.interaction_constraint g f

example (g : ℂ) (f : GUT.ScalarInputAdapter.Input g)
    (p : GUT.PolynomialScalarEOM.OffShell) :
    GUT.ScalarInputAdapter.equiv g f (GUT.PolynomialScalarEOM.integrated g p) = f.val p := by
  simp

example (g : ℂ) : (GUT.RegisteredLagrangianModels.scalar g).input =
    GUT.ScalarLagrangianHelper.input g := GUT.RegisteredLagrangianModels.scalar_input g

def fieldAction := Representation.trivial ℂ Unit (Math.JetLinear.Field Unit)
def directionAction := Representation.trivial ℂ Unit (Math.JetDirections.Direction Unit)

-- Old Math names and import routes still expose both coefficient interfaces.
example : Function.Bijective
    (Math.MixedOperatorInput.nonDerivativeEquiv fieldAction fieldAction directionAction 1 1) :=
  (Math.MixedOperatorInput.nonDerivativeEquiv fieldAction fieldAction directionAction 1 1).bijective
example : Function.Bijective
    (Math.MixedOperatorInput.coefficientEquiv fieldAction fieldAction directionAction 1 1 1) :=
  (Math.MixedOperatorInput.coefficientEquiv fieldAction fieldAction directionAction 1 1 1).bijective

#check Math.ProhibitionInput.no_shared_iff
#check Physics.ScalarInputAdapter.interaction_constraint

end Physics.LegacyInputControl
