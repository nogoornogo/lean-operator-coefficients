import Math.RepresentationTheory.SU2.TwistedSU2ClebschGordan
import Physics.StandardModel.Operators.Higgs.NeutralHiggsPowers

/-! Actual Higgs tensor constituents on the full SM gauge/Weyl/residual group. -/
namespace Physics.SMHiggsConstituents
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor
open scoped TensorProduct
variable {H : Type*} [Group H]

def weakProjection : NeutralHiggsPowers.G H →* WeakDoubletScalars.Group where
  toFun g := g.1.1.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

def hyperProjection : NeutralHiggsPowers.G H →* Circle where
  toFun g := g.1.1.2.2
  map_one' := rfl
  map_mul' _ _ := rfl

def character : NeutralHiggsPowers.G H →* ℂˣ :=
  Circle.toUnits.comp ((zpowGroupHom (3 : ℤ)).comp hyperProjection)

@[simp] theorem character_apply (g : NeutralHiggsPowers.G H) :
    (character g : ℂ) = phase 3 g.1.1 := rfl

def higgsEquiv : Representation.Equiv (NeutralHiggsPowers.higgs (H := H))
    (TwistedSU2ClebschGordan.higgs (weakProjection (H := H)) character) where
  toLinearEquiv := .refl ℂ _
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change phase 3 g.1.1 • Matrix.toLin' (g.1.1.2.1 : Matrix (Fin 2) (Fin 2) ℂ) v =
      (character g : ℂ) • (g.1.1.2.1 : Matrix (Fin 2) (Fin 2) ℂ).mulVec v
    rw [character_apply]
    rfl

theorem higgs_eq : NeutralHiggsPowers.higgs (H := H) =
    TwistedSU2ClebschGordan.higgs (weakProjection (H := H)) character := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact higgsEquiv.toIntertwiningMap.isIntertwining _ _ g v

abbrev Bosons (h d : ℕ) := ((NeutralHiggsPowers.higgs (H := H)).symmetricPower h).tprod
  ((NeutralHiggsPowers.higgs (H := H)).dual.symmetricPower d)

def equivalence (h d : ℕ) : Representation.Equiv (Bosons (H := H) h d)
    (FiniteBlockHom.action (TwistedSU2ClebschGordan.summand (weakProjection (H := H)) character h d)) :=
  by
    unfold Bosons
    rw [higgs_eq]
    generalize hj : weakProjection (H := H) = j
    generalize hc : character (H := H) = χ
    exact TwistedSU2ClebschGordan.equivalence (Γ := NeutralHiggsPowers.G H) j χ h d

@[simp] theorem common_charge (h d : ℕ) (g : NeutralHiggsPowers.G H) :
    (TwistedSU2ClebschGordan.charge (character (H := H)) h d g : ℂ) =
      phase 3 g.1.1 ^ h * phase 3 g.1.1 ^ (-(d : ℤ)) := by
  simp [TwistedSU2ClebschGordan.charge,character_apply,zpow_neg]

end
end Physics.SMHiggsConstituents
