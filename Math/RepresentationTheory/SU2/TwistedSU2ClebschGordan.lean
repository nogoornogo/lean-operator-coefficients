import Math.RepresentationTheory.Constructions.CharacterTwistTransport
import Math.RepresentationTheory.SU2.SU2ClebschGordan

/-! SU2 constituent decomposition retaining a scalar character of the full group. -/
namespace Math.TwistedSU2ClebschGordan
set_option autoImplicit false
noncomputable section
open Representation WeakDoubletScalars
open scoped TensorProduct
variable {Γ : Type*} [Group Γ] (j : Γ →* WeakDoubletScalars.Group) (χ : Γ →* ℂˣ)

abbrev higgs := charTwist χ (doublet.comp j)
abbrev Bosons (h d : ℕ) := ((higgs j χ).symmetricPower h).tprod ((higgs j χ).dual.symmetricPower d)
abbrev charge (h d : ℕ) := χ^h * χ⁻¹^d
def summand (h d : ℕ) (r : SU2ClebschGordan.Index h d) :=
  charTwist (charge χ h d) ((SU2ClebschGordan.summand h d r).comp j)

def symmetricPullback {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : Representation ℂ WeakDoubletScalars.Group V) (m : ℕ) : Representation.Equiv
    (Representation.symmetricPower (a.comp j) m) ((a.symmetricPower m).comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by rfl

def dualPullback : Representation.Equiv (Representation.dual (doublet.comp j)) (doublet.dual.comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro v
    change φ (doublet (j g⁻¹) v) = φ (doublet (j g)⁻¹ v)
    rw [map_inv]

def leftPower (h : ℕ) : Representation.Equiv ((higgs j χ).symmetricPower h)
    (charTwist (χ^h) ((doublet.symmetricPower h).comp j)) :=
  (CharacterTwistTransport.symmetric χ (doublet.comp j) h).trans
    (CharacterTwistTransport.alongEquiv (χ^h) (symmetricPullback j doublet h))

def rightPower (d : ℕ) : Representation.Equiv ((higgs j χ).dual.symmetricPower d)
    (charTwist (χ⁻¹^d) ((doublet.dual.symmetricPower d).comp j)) :=
  ((CharacterTwistTransport.dual χ (doublet.comp j)).symmetricPower d).trans
    ((CharacterTwistTransport.symmetric χ⁻¹ (Representation.dual (doublet.comp j)) d).trans
      (CharacterTwistTransport.alongEquiv (χ⁻¹^d)
        (((dualPullback j).symmetricPower d).trans (symmetricPullback j doublet.dual d))))

def bosonsPullback (h d : ℕ) : Representation.Equiv
    (Representation.tprod ((doublet.symmetricPower h).comp j) ((doublet.dual.symmetricPower d).comp j))
    (((doublet.symmetricPower h).tprod (doublet.dual.symmetricPower d)).comp j) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by rfl

def twistedBosons (h d : ℕ) : Representation.Equiv (Bosons j χ h d)
    (charTwist (charge χ h d)
      (((doublet.symmetricPower h).tprod (doublet.dual.symmetricPower d)).comp j)) :=
  (ExternalInvariantTensor.tensorEquiv (leftPower j χ h) (rightPower j χ d)).trans
    ((CharacterTwistTransport.tensor (χ^h) (χ⁻¹^d) _ _).trans
      (CharacterTwistTransport.alongEquiv
        (V := Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d (Module.Dual ℂ Doublet))
        (W := Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d (Module.Dual ℂ Doublet))
        (charge χ h d) (bosonsPullback j h d)))

def constituentPullback (h d : ℕ) : Representation.Equiv
    (charTwist (charge χ h d) ((FiniteBlockHom.action (SU2ClebschGordan.summand h d)).comp j))
    (FiniteBlockHom.action (summand j χ h d)) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    ext r
    rfl

def equivalence (h d : ℕ) : Representation.Equiv (Bosons j χ h d)
    (FiniteBlockHom.action (summand j χ h d)) :=
  (twistedBosons j χ h d).trans
    ((CharacterTwistTransport.alongEquiv
      (V := Sym[ℂ]^h Doublet ⊗[ℂ] Sym[ℂ]^d (Module.Dual ℂ Doublet))
      (W := ∀ r : SU2ClebschGordan.Index h d, SU2ClebschGordan.Carrier h d r)
      (charge χ h d)
      (SplitRepresentationProjection.restrictEquiv (SU2ClebschGordan.dualEquivalence h d) j)).trans
      (constituentPullback j χ h d))

end
end Math.TwistedSU2ClebschGordan
