import Physics.FieldTheory.Mass.SplitWeylMass
import GUT.SU6.Adapters.StandardSMResidualTensor

open Math

/-!
# A full-gauge-invariant 27-dimensional mass benchmark

The light space is the all-left-handed SM representation. A six-dimensional
heavy representation and its dual are paired by an actual symmetric mass.
This is a post-breaking construction. `StandardSMUVFields` separately
identifies its neutral specialization with the restriction of the actual
analytic SU(6) 15 + 2 bar6 direct-product representation.
-/

set_option autoImplicit false

namespace GUT.StandardSMFullGaugeMass

noncomputable section

open SMEpsilonTensor StandardSMGaugeTensor StandardSMResidualTensor
open StandardBranchProtonObstruction FiniteAbelianChargeSectors

variable {H : Type*} [CommGroup H]

abbrev Light := Quark × (Module.Dual ℂ Color ×
  (Module.Dual ℂ Color × (Weak × Module.Dual ℂ ℂ)))
abbrev Heavy := Color × (Weak × ℂ)
abbrev Fields := (Light × Heavy) × Module.Dual ℂ Heavy

def quarkRho (k : Charges (ChargeLabel H)) := charged quark k.quark.toMul
def upRho (k : Charges (ChargeLabel H)) := charged upRight (-k.up).toMul
def downRho (k : Charges (ChargeLabel H)) := charged downRight (-k.down).toMul
def leptonRho (k : Charges (ChargeLabel H)) := charged lepton k.lepton.toMul
def electronRho (k : Charges (ChargeLabel H)) := charged electronRight (-k.electron).toMul

def lightRho (k : Charges (ChargeLabel H)) : Representation ℂ (GaugeGroup × H) Light :=
  (quarkRho k).prod ((upRho k).dual.prod
    ((downRho k).dual.prod ((leptonRho k).prod (electronRho k).dual)))

def heavyRho (H : Type*) [CommGroup H] : Representation ℂ (GaugeGroup × H) Heavy :=
  charged ((twist color (-2)).prod
    ((twist weak 3).prod (Representation.trivial ℂ GaugeGroup ℂ))) 1

def rho (k : Charges (ChargeLabel H)) : Representation ℂ (GaugeGroup × H) Fields :=
  SplitWeylMass.representation (lightRho k) (heavyRho H)

def mass (k : Charges (ChargeLabel H)) : InvariantWeylMass.SymmetricMass (rho k) :=
  SplitWeylMass.mass (lightRho k) (heavyRho H)

theorem mem_radical_iff (k : Charges (ChargeLabel H)) (x : Fields) :
    x ∈ (mass k).radical.toSubmodule ↔ x.1.2 = 0 ∧ x.2 = 0 :=
  SplitWeylMass.mem_radical_iff (lightRho k) (heavyRho H) x

abbrev ZeroModes (k : Charges (ChargeLabel H)) := (mass k).radical.toSubmodule

def radicalEquiv (k : Charges (ChargeLabel H)) :
    Representation.Equiv (mass k).radical.toRepresentation (lightRho k) :=
  SplitWeylMass.radicalEquiv (lightRho k) (heavyRho H)

theorem light_finrank : Module.finrank ℂ Light = 15 := by
  simp [Light, Quark, Color, Weak, Module.finrank_prod, Module.finrank_tensorProduct,
    Subspace.dual_finrank_eq]

theorem heavy_finrank : Module.finrank ℂ Heavy = 6 := by
  simp [Heavy, Color, Weak, Module.finrank_prod]

theorem fields_finrank : Module.finrank ℂ Fields = 27 := by
  simp [Fields, Light, Heavy, Quark, Color, Weak, Module.finrank_prod,
    Module.finrank_tensorProduct, Subspace.dual_finrank_eq]

theorem radical_finrank (k : Charges (ChargeLabel H)) : Module.finrank ℂ (ZeroModes k) = 15 := by
  rw [(radicalEquiv k).toLinearEquiv.finrank_eq]
  exact light_finrank

theorem radical_character (k : Charges (ChargeLabel H)) (g : GaugeGroup × H) :
    Representation.character (V := ZeroModes k) (mass k).radical.toRepresentation g =
      (lightRho k).character g :=
  congrFun (Representation.char_iso (radicalEquiv k)) g

def heavyVector : Heavy := (colorBasis 0, 0)
def heavyCovector : Module.Dual ℂ Heavy :=
  (LinearMap.proj 0).comp (LinearMap.fst ℂ Color (Weak × ℂ))

theorem mass_nonzero (k : Charges (ChargeLabel H)) : (mass k).form ≠ 0 :=
  SplitWeylMass.mass_nonzero (lightRho k) (heavyRho H) heavyVector heavyCovector (by
    simp [heavyVector, heavyCovector, colorBasis])

end

end GUT.StandardSMFullGaugeMass
