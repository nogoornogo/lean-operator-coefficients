import GUT.Common.StandardChain.StandardChain
import GUT.SU6.Embeddings.StandardSU5Inclusion
import GUT.SU6.Representations.ChargedAmbientRealization
import GUT.SU6.SelectionRules.Models.ProfileZeroModeSupport
import Physics.FieldTheory.Mass.SurjectiveMassDescent
import Math.RepresentationTheory.Characters.UnitarySpectrumRestriction

open Math

/-! Actual SU(6) fields on the standard chain. Descent through the physical
cover preserves the bilinear form, radical and full extracted spectrum.
No inverse to the finite-kernel torus cover, or new support premise, is used. -/

set_option autoImplicit false

namespace GUT.SU6.PhysicalChainSource

noncomputable section

open UnitaryVirtualRealization InvariantWeylMass StandardSU5Inclusion SU5TorusCompatibility
open StandardAbelianCharge FiniteAbelianChargeSectors StandardWeylDualTarget

variable {H : Type*} [CommGroup H]
  (R : ActualUnitaryGroupRepresentation (ChargedAmbientRealization.AmbientGroup H))

def physicalFields := R.restrict (ChargedAmbientRealization.physicalInclusion (-2) 3)

abbrev torusAction := R.rho.comp (StandardChain.torusInclusion inclusion)

theorem action_comp : (torusAction R).comp cover = (physicalFields R).rho := by
  apply MonoidHom.ext
  intro g
  change R.rho (inclusion (SU5.MaximalTorus.hom (torusCover g.1)), g.2) = _
  rw [inclusion_torus]
  rfl

variable (B : SymmetricMass (physicalFields R).rho)

def coveredMass : SymmetricMass ((torusAction R).comp cover) where
  form := B.form
  symmetric := B.symmetric
  invariant g x y := by
    have he := DFunLike.congr_fun (action_comp R) g
    change B.form (((torusAction R).comp cover) g x) (((torusAction R).comp cover) g y) = _
    rw [he]
    exact B.invariant g x y

def mass : SymmetricMass (torusAction R) :=
  SymmetricMass.descend (torusAction R) cover cover_surjective (coveredMass R B)

@[simp] theorem mass_form : (mass R B).form = B.form := rfl

theorem radical_submodule : (mass R B).radical.toSubmodule = B.radical.toSubmodule := rfl

theorem radical_comp : (mass R B).radical.toRepresentation.comp cover =
    B.radical.toRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((torusAction R).comp cover) g x.val = (physicalFields R).rho g x.val
  rw [action_comp]
  rfl

def radicalEquiv : Representation.Equiv
    ((mass R B).radical.toRepresentation.comp cover) B.radical.toRepresentation :=
  .mk (LinearEquiv.refl ℂ _) (by
    intro g
    change ((mass R B).radical.toRepresentation.comp cover) g = B.radical.toRepresentation g
    rw [radical_comp]
    rfl)

theorem radical_character (g : StandardSMCharacterTarget.CombinedGroup H) :
    (mass R B).radical.toRepresentation.character (cover g) =
      B.radical.toRepresentation.character g := by
  change Representation.character ((mass R B).radical.toRepresentation.comp cover) g = _
  rw [radical_comp]
  rfl

theorem hasTarget (P : FiniteChargeProfiles.Profiles (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (physicalFields R) B P s) :
    SU5.TorusMassSource.HasTarget (StandardChain.pullback inclusion R.rho) (mass R B) P s := by
  intro t
  change (mass R B).radical.toRepresentation.character t -
    (mass R B).radical.toRepresentation.dual.character t = _
  obtain ⟨g, rfl⟩ := cover_surjective t
  rw [Representation.char_dual, ← map_inv, radical_character, radical_character]
  have he := ht g
  rw [lightDualIndex, dualIndex_character, Representation.char_dual] at he
  exact he.trans ((StandardSMCharacterTarget.character_ofCharacter _ g.1.toAdd g.2).trans
    (eval_eq _ g.1.toAdd g.2).symm)

theorem spectrum_eq :
    SU5.TorusMassSource.spectrum (StandardChain.pullback inclusion R.rho)
        (StandardChain.pullback_unitary inclusion R.rho R.unitary) (mass R B) =
      ProfileZeroModeSupport.spectrum (physicalFields R) B := by
  let hu := AbelianMassSpectrum.radical_unitary (mass R B)
    (SU5.TorusMassSource.restricted_unitary (StandardChain.pullback inclusion R.rho)
      (StandardChain.pullback_unitary inclusion R.rho R.unitary))
  have hs : UnitaryCharacterSpectrum.spectrum
      ((mass R B).radical.toRepresentation.comp cover)
      (UnitaryCharacterSpectrum.comp_unitary _ hu cover) =
      AbelianActualSpectrum.spectrum (ProfileZeroModeSupport.radicalRepresentation (physicalFields R) B) := by
    apply AbelianActualSpectrum.eval_injective
    intro g
    rw [UnitaryCharacterSpectrum.spectrum_eval, AbelianActualSpectrum.spectrum_eval]
    exact radical_character R B g
  ext key
  change UnitaryCharacterSpectrum.spectrum (mass R B).radical.toRepresentation hu
    (SU5.TorusCharacter.keyCharacter key) = _
  rw [← UnitaryCharacterSpectrum.spectrum_comp_apply _ hu cover cover_surjective,
    key_comp_cover, hs]
  rfl

def model (F : FiniteChargeProfiles.Family (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (physicalFields R) B F.profiles s) :
    StandardChain.Model inclusion R.rho where
  unitary := R.unitary
  mass := mass R B
  profile := F
  singlets := s
  lightTarget := hasTarget R B F.profiles s ht

theorem model_spectrum (F : FiniteChargeProfiles.Family (ChargeLabel H)) (s : ChargeLabel H →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (physicalFields R) B F.profiles s) :
    (model R B F s ht).lightSpectrum = ProfileZeroModeSupport.spectrum (physicalFields R) B :=
  spectrum_eq R B

end

end GUT.SU6.PhysicalChainSource
