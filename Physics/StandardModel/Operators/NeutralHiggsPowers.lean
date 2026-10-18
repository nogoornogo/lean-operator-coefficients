import Physics.StandardModel.Operators.BnvMixedInput
import Physics.FieldTheory.Mass.LightInheritanceBoundary
import Physics.FieldTheory.Mass.EquivariantWeylMassTransport
import Math.RepresentationTheory.MixedInvariantDressing
import Mathlib.LinearAlgebra.Pi
import Math.RepresentationTheory.ExternalUnitEquivalence
import Physics.StandardModel.Operators.BnvSevenModelInterface

namespace GUT.NeutralHiggsPowers
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor BnvMixedInput
open scoped TensorProduct
variable {H : Type*} [Group H]
abbrev G (H : Type*) := (GaugeGroup × WeylSpinor.Group) × H
abbrev Multiplicity (_ : ScalarSpecies) := ℂ
abbrev Fields := ∀ u : ScalarSpecies, ScalarField (S := Multiplicity) u
local instance : AddCommGroup Fields := inferInstance

def flavor (u : ScalarSpecies) : Representation ℂ H (Multiplicity u) := trivial ℂ H ℂ
def action : Representation ℂ (G H) Fields := scalarRepresentation flavor
def higgs : Representation ℂ (G H) SMEpsilonTensor.Weak :=
  (scalarGauge 0).comp ((MonoidHom.fst GaugeGroup WeylSpinor.Group).comp
    (MonoidHom.fst (GaugeGroup × WeylSpinor.Group) H))

def coordinates : Representation.Equiv (action (H := H)) ((higgs (H := H)).prod (higgs (H := H)).dual) := by
  let e := BnvSevenModelInterface.piEquiv (fun u : ScalarSpecies =>
    ExternalUnitEquivalence.equiv (H := H)
      ((scalarGauge u).comp (MonoidHom.fst GaugeGroup WeylSpinor.Group)))
  refine e.trans ?_
  refine Representation.Equiv.mk (LinearEquiv.piFinTwo ℂ (fun u => ScalarGaugeCarrier u)) ?_
  intro g
  apply LinearMap.ext
  intro x
  rfl

def pairing : InvariantWeylMass.SymmetricMass (action (H := H)) :=
  EquivariantWeylMassTransport.pullback (coordinates (H := H)) (LightInheritanceBoundary.pairedMass (higgs (H := H)))

def vector : Fields := (coordinates (H := H)).symm (Pi.single 0 1,LinearMap.proj 0)

theorem pairing_diagonal : (pairing (H := H)).form (vector (H := H)) (vector (H := H)) = 2 := by
  rw [pairing,EquivariantWeylMassTransport.pullback_apply]
  norm_num [vector,LightInheritanceBoundary.pairedMass,InvariantWeylMass.ofDirac,
    DiracWeylConvention.massBilinear]

def coefficient (r : ℕ) : IntertwiningMap ((action (H := H)).symmetricPower (r*2)) (trivial ℂ (G H) ℂ) :=
  InvariantQuadraticPowers.invariant (action (H := H)) (pairing (H := H)).form (pairing (H := H)).invariant r

theorem coefficient_nonzero (r : ℕ) : coefficient (H := H) r ≠ 0 := by
  apply InvariantQuadraticPowers.invariant_nonzero _ _ _ r (vector (H := H))
  rw [pairing_diagonal]
  norm_num

def normalization (r : ℕ) : ℂ :=
  (Fintype.card (Equiv.Perm (Fin (r*2))) : ℂ) * (2 : ℂ)^r

theorem normalization_nonzero (r : ℕ) : normalization r ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast Fintype.card_ne_zero
  · exact pow_ne_zero r (by norm_num)

def normalized (r : ℕ) : IntertwiningMap ((action (H := H)).symmetricPower (r*2)) (trivial ℂ (G H) ℂ) :=
  (normalization r)⁻¹ • coefficient r

theorem normalized_nonzero (r : ℕ) : normalized (H := H) r ≠ 0 := by
  exact smul_ne_zero (inv_ne_zero (normalization_nonzero r)) (coefficient_nonzero r)

theorem pairing_polynomial (x : Fields) : (pairing (H := H)).form x x =
    2 * ((coordinates (H := H)) x).2 (((coordinates (H := H)) x).1) := by
  rw [pairing,EquivariantWeylMassTransport.pullback_apply]
  change ((coordinates (H := H)) x).2 (((coordinates (H := H)) x).1) +
    ((coordinates (H := H)) x).2 (((coordinates (H := H)) x).1) = _
  ring

/-- The diagonal polynomial is exactly (H-dagger H)^r after normalization. -/
theorem normalized_diagonal (r : ℕ) (x : Fields) :
    normalized (H := H) r (SymmetricPower.tprod ℂ (fun _ => x)) =
      (((coordinates (H := H)) x).2 (((coordinates (H := H)) x).1))^r := by
  change (normalization r)⁻¹ * InvariantQuadraticPowers.coefficient (pairing (H := H)).form r
    (SymmetricPower.tprod ℂ (fun _ => x)) = _
  rw [InvariantQuadraticPowers.diagonal,pairing_polynomial,mul_pow]
  have he : (normalization r)⁻¹ *
      ((Fintype.card (Equiv.Perm (Fin (r*2))) : ℂ) *
        ((2 : ℂ)^r * (((coordinates (H := H)) x).2 (((coordinates (H := H)) x).1))^r)) =
      ((normalization r)⁻¹ * normalization r) *
        (((coordinates (H := H)) x).2 (((coordinates (H := H)) x).1))^r := by
    unfold normalization
    ring
  rw [he,inv_mul_cancel₀ (normalization_nonzero r),one_mul]
end
end GUT.NeutralHiggsPowers
