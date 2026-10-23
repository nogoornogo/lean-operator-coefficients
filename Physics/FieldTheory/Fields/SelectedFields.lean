import Math.RepresentationTheory.Fields.Interactions
import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Physics.FieldTheory.Spinor.Weyl.WeylSpinor

/-! Physical constructors for the shared selected-field interface. Weyl chirality
is specified separately from the internal contragredient. Independent formal
conjugate fields do not acquire an analytic reality condition here. -/
namespace Physics.SelectedFields
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct
variable {G U V : Type*} [Group G] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup V] [Module ℂ V]
  {rho : Representation ℂ G U} {tau : Representation ℂ G V}

def mass (B : InvariantWeylMass.SymmetricMass rho) : Subrepresentation rho :=
  FieldSelection.kernel B.toIntertwiningMap

theorem mass_eq_radical (B : InvariantWeylMass.SymmetricMass rho) : mass B = B.radical := by
  apply Subrepresentation.toSubmodule_injective
  rfl

def dirac (M : IntertwiningMap rho tau) : Subrepresentation rho := FieldSelection.kernel M

def massDictionary (B : InvariantWeylMass.SymmetricMass rho)
    (e : IntertwiningMap tau rho) (p : U →ₗ[ℂ] V)
    (he : ∀ v, B.form (e v) = 0) (hp : ∀ v, p (e v) = v)
    (hs : ∀ u, B.form u = 0 → e (p u) = u) : Equiv tau (mass B).toRepresentation :=
  FieldSelection.ofMaps (mass B) e p he hp hs

/-- `true` specifies the conjugated right Weyl action; internal duality is
not used to infer a chirality. -/
def spin (rightHanded : Bool) : Representation ℂ WeylSpinor.Group WeylSpinor.Space :=
  if rightHanded then WeylSpinor.right else WeylSpinor.left

def withWeyl (rightHanded : Bool) (e : Equiv rho tau) :
    Equiv (ExternalInvariantTensor.external rho (spin rightHanded))
      (ExternalInvariantTensor.external tau (spin rightHanded)) :=
  ExternalInvariantTensor.externalEquiv e (Representation.Equiv.refl _)

theorem withWeyl_pure (rightHanded : Bool) (e : Equiv rho tau) (u : U)
    (s : WeylSpinor.Space) : withWeyl rightHanded e (u ⊗ₜ[ℂ] s) = e u ⊗ₜ[ℂ] s := by
  exact TensorProduct.congr_tmul _ _ _ _

def internalDual (e : Equiv rho tau) : Equiv rho.dual tau.dual :=
  SplitRepresentationProjection.dualEquiv e

theorem internalDual_pair (e : Equiv rho tau) (f : Module.Dual ℂ U) (u : U) :
    internalDual e f (e u) = f u :=
  congrArg f (e.toLinearEquiv.symm_apply_apply u)

end
end Physics.SelectedFields
