import Math.RepresentationTheory.Multiplicity.MultiplicityUnitaryCentralizer
import Math.RepresentationTheory.FamilyStabilizer

/-! The actual gauge-commuting unitary mixing group as a candidate flavor
action. Preserving specified interaction tensors is an additional condition. -/
namespace Math.FlavorCandidate
set_option autoImplicit false
noncomputable section
open UnitaryCentralizerTransport
open scoped MonoidAlgebra
variable {G E : Type*} [Group G] [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  (rho : Representation ℂ G E)

def action : Representation ℂ (unitaryCentralizer rho) E where
  toFun u := u.val.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

theorem action_commutes (u : unitaryCentralizer rho) (g : G) (x : E) :
    action rho u (rho g x) = rho g (action rho u x) :=
  congrArg (fun T : E →L[ℂ] E => T x) (u.property g).eq

theorem action_faithful : Function.Injective (action rho) := by
  intro u v h
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  exact LinearMap.congr_fun h x

/-- Every actual unitary gauge-commuting operator is in the candidate group. -/
def ofOperator (T : unitary (E →L[ℂ] E))
    (h : ∀ g x, T.val (rho g x) = rho g (T.val x)) : unitaryCentralizer rho :=
  ⟨T, fun g => by
    apply ContinuousLinearMap.ext
    intro x
    exact h g x⟩

variable (D : MultiplicityCommutant.Model ℂ[G] rho.asModule)
  [Fintype (isotypicComponents ℂ[G] rho.asModule)]

/-- Reuse the exact multiplicity classification; interactions can reduce this group. -/
def coordinates (h : UnitaryMultiplicity.IsUnitaryRepresentation rho) :
    unitaryCentralizer rho ≃ₜ* Π c, Matrix.unitaryGroup (Fin (D.multiplicity c)) ℂ :=
  MultiplicityUnitaryCentralizer.unitaryCentralizerEquiv rho D h

end
end Math.FlavorCandidate
