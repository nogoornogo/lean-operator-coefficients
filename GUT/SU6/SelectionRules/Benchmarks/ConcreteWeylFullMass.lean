import GUT.SU6.SelectionRules.Benchmarks.ConcreteWeylNonzeroMass
import GUT.SU6.Adapters.AbelianCharacterBasis
import Physics.FieldTheory.Mass.Algebra.HyperbolicBasisMass
import GUT.SU6.SelectionRules.StandardBranch.WeylZeroModeSupport

open Physics

open Math

/-!
# A fifteen-dimensional SM radical for the standard Weyl benchmark

The fields are still the canonical 15 + 2 bar6. Their restricted character
is SM + 6 + bar6. A prescribed actual eigenbasis pairs the last two summands
(including their neutral singlets), leaving precisely the SM character.
Invariance is under the model's compact four-torus times the residual group.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace GUT.ConcreteWeylFullMass

noncomputable section

open StandardSMCharacterTarget StandardWeylMassSource InvariantWeylMass
open ConcreteWeylBenchmark ConcreteSU6Representations ConcreteSU6PhysicalTarget
open ConcreteSU6Branching
open ConcreteWeylNonzeroMass (weightHom weightHom_apply)

variable {H : Type*} [CommGroup H]

abbrev Index := HyperbolicBasisMass.Index (Fin 15) (Fin 6)

def label : Index → CombinedGroup H →* ℂ := Sum.elim
  (fun i => weightHom (PhysicalTorusCharacterBridge.smExponent i))
  (Sum.elim (fun i => weightHom (fundamentalExponent i))
    (fun i => weightHom (-fundamentalExponent i)))

theorem fields_character_sum (g : CombinedGroup H) :
    (ordinaryFields (matter H)).rho.character g = ∑ i : Index, label i g := by
  have hs := ConcreteWeylBenchmark.signed_target_eval g.1.toAdd g.2
  rw [neutral_target_eval, eval_integralSMCharacter] at hs
  have hf : fundamental.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 g.1) =
      ∑ i : Fin 6, UnitAddTorus.mFourier (fundamentalExponent i) g.1.toAdd := by
    change fundamental.rho.character
      (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd g.1.toAdd)) = _
    rw [PhysicalSMTorusTarget.embedding_ofAdd, fundamental_character]
    simp_rw [physicalDiagonalPoint_coords]
  have ha : antifundamental.rho.character (PhysicalSMTorusTarget.embedding (-2) 3 g.1) =
      ∑ i : Fin 6, UnitAddTorus.mFourier (-fundamentalExponent i) g.1.toAdd := by
    change antifundamental.rho.character
      (PhysicalSMTorusTarget.embedding (-2) 3 (Multiplicative.ofAdd g.1.toAdd)) = _
    rw [PhysicalSMTorusTarget.embedding_ofAdd, antifundamental_character]
    simp_rw [physicalDiagonalPoint_coords, mFourier_neg_eq_inv]
  change (ordinaryFields (matter H)).rho.character (Multiplicative.ofAdd g.1.toAdd, g.2) = _
  rw [ConcreteWeylBenchmark.fields_character]
  simp only [Fintype.sum_sum_type, label, Sum.elim_inl, Sum.elim_inr, weightHom_apply]
  rw [← hf, ← ha, hs]
  simp only [ofAdd_toAdd]
  ring

def eigenbasis : Module.Basis Index ℂ (ordinaryFields (matter H)).V :=
  AbelianCharacterBasis.prescribedBasis (ordinaryFields (matter H)) label fields_character_sum

theorem eigenbasis_action (g : CombinedGroup H) (i : Index) :
    (ordinaryFields (matter H)).rho g (eigenbasis i) = label i g • eigenbasis i :=
  AbelianCharacterBasis.prescribedBasis_action (ordinaryFields (matter H)) label fields_character_sum g i

theorem labels_pair (i : Fin 6) (g : CombinedGroup H) :
    label (.inr (.inl i)) g * label (.inr (.inr i)) g = 1 := by
  change UnitAddTorus.mFourier (fundamentalExponent i) g.1.toAdd *
    UnitAddTorus.mFourier (-fundamentalExponent i) g.1.toAdd = 1
  rw [← UnitAddTorus.mFourier_add, add_neg_cancel, UnitAddTorus.mFourier_zero]
  rfl

def fullMass : SymmetricMass (ordinaryFields (matter H)).rho :=
  HyperbolicBasisMass.mass eigenbasis (ordinaryFields (matter H)).rho label eigenbasis_action labels_pair

theorem fullMass_nonzero : (fullMass (H := H)).form ≠ 0 :=
  HyperbolicBasisMass.form_ne_zero (eigenbasis (H := H)) (0 : Fin 6)

theorem fullMass_radical_finrank :
    Module.finrank ℂ (fullMass (H := H)).radical.toSubmodule = 15 :=
  HyperbolicBasisMass.radical_finrank eigenbasis (ordinaryFields (matter H)).rho label
    eigenbasis_action labels_pair

/-- Full actual radical character, not just its antisymmetrization. -/
theorem fullMass_radical_character (g : CombinedGroup H) :
    (fullMass (H := H)).radical.toRepresentation.character g =
      eval (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0)
        g.1.toAdd g.2 := by
  rw [neutral_target_eval, eval_integralSMCharacter]
  exact HyperbolicBasisMass.radical_character eigenbasis (ordinaryFields (matter H)).rho label
    eigenbasis_action labels_pair g

def model (H : Type*) [CommGroup H] : StandardWeylModel H where
  matter := matter H
  nonnegative := matter_nonnegative
  mass := fullMass
  generations := 1
  generations_ne := by norm_num
  charges := uniformCharges 0
  singlets := 0
  lightTarget := mass_hasDualSMTarget _

theorem fullMass_actualSpectrum :
    AbelianActualSpectrum.spectrum (WeylZeroModeSupport.lightRepresentation (model H)) =
      WeylZeroModeSupport.lift
        (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0) := by
  apply AbelianActualSpectrum.eval_injective
  intro g
  rw [AbelianActualSpectrum.spectrum_eval, WeylZeroModeSupport.eval_lift]
  exact fullMass_radical_character g

theorem model_lightSpectrum : WeylZeroModeSupport.lightSpectrum (model H) =
    exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0 := by
  ext key
  rw [WeylZeroModeSupport.lightSpectrum_apply, fullMass_actualSpectrum]
  exact Finsupp.mapDomain_apply_of_injective keyMonoidHom_injective _ key

theorem exists_exact_sm_radical (H : Type*) [CommGroup H] :
    ∃ M : StandardWeylModel H, M.generations = 1 ∧ M.mass.form ≠ 0 ∧
      Module.finrank ℂ M.mass.radical.toSubmodule = 15 ∧
      WeylZeroModeSupport.lightSpectrum M =
        exactSMWithSingletsResolvedCharacter 1 (uniformCharges 0) 0 :=
  ⟨model H, rfl, fullMass_nonzero, fullMass_radical_finrank, model_lightSpectrum⟩

end

end GUT.ConcreteWeylFullMass
