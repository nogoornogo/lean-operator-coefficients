import Physics.StandardModel.Operators.InverseLeptonParitySelection
import Physics.StandardModel.Operators.InverseCyclicSMCharges
import Mathlib.LinearAlgebra.Dual.Basis
import Physics.FieldTheory.Mass.ConstructedSpectatorRadical
import Math.RepresentationTheory.Decomposition.ExternalCopyFactorization
import Math.RepresentationTheory.Multiplicity.FiniteSpectrum

/-! Actual three-generation lepton-parity carriers and spectator mass. -/
namespace GUT.InverseCyclicSMRealization
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor ExternalInvariantTensor
open DeltaLOneSignedInput InvariantWeylMass
open scoped TensorProduct
abbrev H := CyclicCharge.Group 2
abbrev Flavor := Fin 3 → ℂ
abbrev G := GaugeGroup × H

/-- All-left chiral species, distinct from the ten-species signed alphabet. -/
def index : Fin 5 → Species := ![0,6,7,3,9]
abbrev Carrier (i : Fin 5) := DeltaLOneSignedFields.GaugeCarrier (index i) ⊗[ℂ] Flavor
instance (i : Fin 5) : AddCommGroup (Carrier i) := inferInstance
instance (i : Fin 5) : Module ℂ (Carrier i) := inferInstance

def species (i : Fin 5) : Representation ℂ G (Carrier i) :=
  external (DeltaLOneSignedFields.gauge (index i))
    (InverseLeptonParitySelection.copies (V := Flavor) (lepton (index i)))
def gaugeSpecies (i : Fin 5) : Representation ℂ GaugeGroup (Carrier i) :=
  (DeltaLOneSignedFields.gauge (index i)).tprod (trivial ℂ GaugeGroup Flavor)

abbrev Light := ∀ i : Fin 5, Carrier i
def light : Representation ℂ G Light := FiniteSpeciesExterior.representation species
def sm : Representation ℂ GaugeGroup Light := FiniteSpeciesExterior.representation gaugeSpecies

theorem species_gauge (i : Fin 5) : ProductFactorization.firstRestriction (species i) = gaugeSpecies i := by
  apply MonoidHom.ext
  intro g
  apply TensorProduct.ext'
  intro v w
  simp [ProductFactorization.firstRestriction,species,gaugeSpecies,external,
    InverseLeptonParitySelection.copies,Representation.tprod_apply]

theorem gauge_restriction : ProductFactorization.firstRestriction light = sm := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  funext i
  exact LinearMap.congr_fun (congrArg (fun r => r g) (species_gauge i)) (v i)

def threeCopies (i : Fin 5) : Equiv (gaugeSpecies i)
    (FiniteSpectrum.copies 3 (DeltaLOneSignedFields.gauge (index i))) :=
  .mk (ExternalCopyFactorization.coordinates (Pi.basisFun ℂ (Fin 3))) (by
    intro g
    apply TensorProduct.ext'
    intro v w
    funext j
    simp [ExternalCopyFactorization.coordinates_tmul,gaugeSpecies,Representation.tprod_apply,
      FiniteSpectrum.copies_apply])

/-- A genuinely charged singlet spectator and its contragredient pair. -/
def spectator : Representation ℂ G ℂ :=
  (CyclicCharge.representation (1 : ZMod 2)).comp (MonoidHom.snd GaugeGroup H)
def original := ConstructedSpectatorRadical.action light spectator
def mass : SymmetricMass original := ConstructedSpectatorRadical.mass light spectator
def radicalEquiv : Equiv mass.radical.toRepresentation light :=
  ConstructedSpectatorRadical.radicalEquiv light spectator

theorem spectator_mass_nonzero : mass.form ≠ 0 := by
  intro h
  have he := LinearMap.congr_fun (LinearMap.congr_fun h
    ((0 : Light), ((1 : ℂ), (0 : Module.Dual ℂ ℂ))))
    ((0 : Light), ((0 : ℂ), LinearMap.id))
  norm_num [mass,ConstructedSpectatorRadical.mass,OrthogonalMass.prod,
    LightInheritanceBoundary.pairedMass,ofDirac] at he

/-- The coefficient alphabet uses three flavor coordinates and one Higgs
coordinate; the conjugate species have their declared opposite actions. -/
abbrev fermionFlavor (u : Species) := InverseLeptonParitySelection.flavor (F := fun _ => Flavor) u
abbrev higgsFlavor (u : BnvMixedInput.ScalarSpecies) :=
  InverseLeptonParitySelection.scalarFlavor (S := fun _ => ℂ) u

theorem coefficient_species (i : Fin 5) : species i =
    external (DeltaLOneSignedFields.gauge (index i)) (fermionFlavor (index i)) := rfl

theorem all_B1_forbidden : ∀ n m,
    ∀ f : ComposableBLSupport.Input fermionFlavor higgsFlavor InverseLeptonParitySelection.target n m, f = 0 :=
  InverseLeptonParitySelection.all_forbidden
def coefficientGroup : (G × WeylSpinor.Group) →*
    ((GaugeGroup × WeylSpinor.Group) × H) where
  toFun g := ((g.1.1,g.2),g.1.2)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem chiral_left (i : Fin 5) : DeltaLOneSignedFields.rightHanded (index i) = false := by
  fin_cases i <;> decide +kernel

/-- The actual light gauge/flavor carrier and the all-degree gauge/spin/flavor
carrier differ only by proved tensor and group regrouping. -/
def physicalFieldEquiv (i : Fin 5) : Equiv (external (species i) WeylSpinor.left)
    ((DeltaLOneSignedFields.field fermionFlavor (index i)).comp coefficientGroup) :=
  .mk
    (((TensorProduct.assoc ℂ (DeltaLOneSignedFields.GaugeCarrier (index i)) Flavor WeylSpinor.Space).trans
      (TensorProduct.congr (LinearEquiv.refl ℂ _) (TensorProduct.comm ℂ Flavor WeylSpinor.Space))).trans
      (TensorProduct.assoc ℂ (DeltaLOneSignedFields.GaugeCarrier (index i)) WeylSpinor.Space Flavor).symm)
    (by
      intro g
      apply TensorProduct.ext'
      intro t u
      induction t using TensorProduct.inductionOn with
      | tmul v x =>
        simp [species,external,DeltaLOneSignedFields.field,DeltaLOneSignedFields.localField,
          FourSameWeylCompleteness.action,chiral_left,coefficientGroup,Representation.tprod_apply,
          fermionFlavor,InverseLeptonParitySelection.flavor,InverseLeptonParitySelection.fq]
      | add t s ht hs => simp only [map_add,TensorProduct.add_tmul,ht,hs])

theorem selected_dictionary (i : Fin 5) :
    (lepton (index i) : ZMod 2) = InverseCyclicSMCharges.chiral 0 1 i := by
  fin_cases i <;> decide +kernel

theorem higgs_residual_neutral (u : BnvMixedInput.ScalarSpecies) (g : H)
    (x : BnvMixedInput.ScalarField (S := fun _ => ℂ) u) :
    BnvMixedInput.scalarField higgsFlavor u (1,g) x = x := by
  simpa [InverseLeptonParitySelection.bq,MixedChargeSelection.cyclicCharacter] using
    InverseLeptonParitySelection.scalar_scalar (S := fun _ => ℂ) g u x

theorem flavorDual_action (q : ZMod 2) (g : H) (phi : Module.Dual ℂ Flavor) :
    (InverseLeptonParitySelection.copies (V := Flavor) q).dual g phi =
      ZMod.stdAddChar ((-q)*g.toAdd) • phi := by
  apply LinearMap.ext
  intro x
  change phi (ZMod.stdAddChar (q*(g⁻¹).toAdd) • x) = _
  rw [map_smul]
  simp

def flavorDualEquiv (q : ZMod 2) : Equiv
    (InverseLeptonParitySelection.copies (V := Flavor) q).dual
    (InverseLeptonParitySelection.copies (V := Flavor) (-q)) :=
  .mk ((Pi.basisFun ℂ (Fin 3)).dualBasis.equiv (Pi.basisFun ℂ (Fin 3)) (Equiv.refl (Fin 3))) (by
    intro g
    apply LinearMap.ext
    intro phi
    simp only [LinearMap.comp_apply]
    rw [flavorDual_action]
    exact map_smul _ _ _)
end
end GUT.InverseCyclicSMRealization
