import Physics.FieldTheory.Mass.Spectrum.SymmetricMassIndex

/-! An invariant mass descends along a surjective group homomorphism when
the field action already factors through it. No inverse chart is chosen. -/

set_option autoImplicit false

namespace Physics.InvariantWeylMass.SymmetricMass

noncomputable section

variable {G K E : Type*} [Group G] [Group K] [AddCommGroup E] [Module ℂ E]
  (rho : Representation ℂ G E) (f : K →* G) (hf : Function.Surjective f)
  (B : SymmetricMass (rho.comp f))

def descend : SymmetricMass rho where
  form := B.form
  symmetric := B.symmetric
  invariant g x y := by
    obtain ⟨k, rfl⟩ := hf g
    exact B.invariant k x y

@[simp] theorem descend_form : (descend rho f hf B).form = B.form := rfl

theorem descend_radical : (descend rho f hf B).radical.toSubmodule = B.radical.toSubmodule := rfl

theorem descend_radical_comp :
    (descend rho f hf B).radical.toRepresentation.comp f = B.radical.toRepresentation := rfl

theorem descend_radical_character [FiniteDimensional ℂ E] (k : K) :
    (descend rho f hf B).radical.toRepresentation.character (f k) =
      B.radical.toRepresentation.character k := rfl

end

end Physics.InvariantWeylMass.SymmetricMass
