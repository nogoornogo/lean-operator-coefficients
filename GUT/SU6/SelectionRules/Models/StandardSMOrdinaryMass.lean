import GUT.SU6.SelectionRules.Models.StandardSMOrdinaryFields
import GUT.SU6.SelectionRules.Models.StandardSMUVMass
import GUT.SU6.SelectionRules.Models.ContinuousWeylMassTransport

open Math

/-!
# The full-gauge mass in the canonical Weyl model

The transported mass extends the original physical-torus interface to the
full standard gauge group. Its actual radical, not just its dual index,
is the fifteen-dimensional all-left-handed SM representation.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

namespace GUT.StandardSMOrdinaryMass

noncomputable section

open StandardSMOrdinaryFields StandardSMUVFields
open StandardWeylMassSource StandardSMCharacterTarget InvariantWeylMass
open SplitRepresentationProjection ConcreteSU6Representations
open ConcreteSU6PhysicalTarget (uniformCharges)

variable (H : Type*) [CommGroup H]

/-- Keep the named UV action in the type of the mass-transport certificate. -/
def uvGaugeEquiv : Representation.Equiv (StandardSMOrdinaryFields.gaugeRho H)
    (StandardSMUVMass.rho H) := StandardSMOrdinaryFields.gaugeEquiv H

def transport :=
  EquivariantWeylMassTransport.certificate (uvGaugeEquiv H)
    (StandardSMUVMass.mass H)

def fullMass := (transport H).mass

def mass : SymmetricMass (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho :=
  EquivariantWeylMassTransport.restrictTo (fullMass H) (torusHom H)
    (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho (gauge_restriction H)

theorem mass_form_eq : (mass H).form = (fullMass H).form := rfl

theorem fullMass_form_eq : (fullMass H).form =
    (EquivariantWeylMassTransport.pullback (StandardSMOrdinaryFields.gaugeEquiv H)
      (StandardSMUVMass.mass H)).form := (transport H).form_eq

theorem mass_nonzero : (mass H).form ≠ 0 := by
  rw [mass_form_eq]
  exact (transport H).nonzero_of (StandardSMUVMass.mass_nonzero H)

abbrev ZeroModes := (mass H).radical.toSubmodule

def fullZeroRho := (fullMass H).radical.toRepresentation

def radicalEquiv := (transport H).radicalEquiv

def lightEquiv :=
  (radicalEquiv H).trans (StandardSMUVMass.lightEquiv H)

theorem zero_restriction :
    (fullZeroRho H).comp (torusHom H) = (mass H).radical.toRepresentation := by
  apply MonoidHom.ext; intro g
  apply LinearMap.ext; intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (DFunLike.congr_fun (gauge_restriction H) g) x.val

def physicalLightEquiv :=
  (EquivariantWeylMassTransport.restrictToRadicalEquiv (fullMass H) (torusHom H)
    (ordinaryFields (ConcreteWeylBenchmark.matter H)).rho (gauge_restriction H)).trans
      (restrictEquiv (lightEquiv H) (torusHom H))

theorem radical_finrank : Module.finrank ℂ (ZeroModes H) = 15 := by
  change Module.finrank ℂ (transport H).mass.radical.toSubmodule = 15
  rw [(lightEquiv H).toLinearEquiv.finrank_eq]
  exact StandardSMFullGaugeMass.light_finrank

theorem light_character (g : CombinedGroup H) :
    (StandardSMFullGaugeMass.lightRho (neutralCharges H)).character (torusHom H g) =
      eval (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0)
        g.1.toAdd g.2 := by
  have ht := congrFun (Representation.char_iso (withResidualEquiv H)) (torusHom H g)
  have hf := congrFun (Representation.char_iso (StandardSMGroup.neutralFundamentalEquiv H))
    (torusHom H g)
  have ha := congrFun (Representation.char_iso
    (restrictEquiv StandardSMGroup.analyticAntifundamentalEquiv
      (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup H))) (torusHom H g)
  have hg : StandardSMGroup.withResidual H (torusHom H g) = physicalHom H g :=
    DFunLike.congr_fun (StandardSMTorus.withResidual_comp H) g
  change uvRho.character (StandardSMGroup.withResidual H (torusHom H g)) = _ at ht
  rw [hg] at ht
  change fundamental.rho.character (StandardSMGroup.withResidual H (torusHom H g)) = _ at hf
  rw [hg] at hf
  change antifundamental.rho.character (StandardSMGroup.withResidual H (torusHom H g)) =
    Representation.character (StandardSMGroup.heavy.dual.comp
      (MonoidHom.fst StandardSMGaugeTensor.GaugeGroup H)) (torusHom H g) at ha
  rw [hg, dual_comp, ← StandardSMGroup.heavyRho_eq] at ha
  have hu : uvRho.character (physicalHom H g) =
      exteriorTwo.rho.character (physicalHom H g) +
        antifundamental.rho.character (physicalHom H g) +
        antifundamental.rho.character (physicalHom H g) := by
    change LinearMap.trace ℂ _ (((exteriorTwo.rho (physicalHom H g)).prodMap
      (antifundamental.rho (physicalHom H g))).prodMap
      (antifundamental.rho (physicalHom H g))) = _
    rw [LinearMap.trace_prodMap', LinearMap.trace_prodMap']
    rfl
  have hd : (StandardSMFullGaugeMass.rho (neutralCharges H)).character (torusHom H g) =
      (StandardSMFullGaugeMass.lightRho (neutralCharges H)).character (torusHom H g) +
        (StandardSMFullGaugeMass.heavyRho H).character (torusHom H g) +
        (StandardSMFullGaugeMass.heavyRho H).dual.character (torusHom H g) := by
    change LinearMap.trace ℂ _ (((StandardSMFullGaugeMass.lightRho (neutralCharges H)
      (torusHom H g)).prodMap (StandardSMFullGaugeMass.heavyRho H (torusHom H g))).prodMap
      ((StandardSMFullGaugeMass.heavyRho H).dual (torusHom H g))) = _
    rw [LinearMap.trace_prodMap', LinearMap.trace_prodMap']
    rfl
  rw [hu, hd, ← hf, ← ha] at ht
  rw [ConcreteWeylBenchmark.signed_target_eval]
  change _ = exteriorTwo.rho.character (physicalHom H g) +
    antifundamental.rho.character (physicalHom H g) - fundamental.rho.character (physicalHom H g)
  linear_combination -ht

theorem radical_character (g : CombinedGroup H) :
    (mass H).radical.toRepresentation.character g =
      eval (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0)
        g.1.toAdd g.2 :=
  (congrFun (Representation.char_iso (physicalLightEquiv H)) g).trans (light_character H g)

def model : StandardWeylModel H where
  matter := ConcreteWeylBenchmark.matter H
  nonnegative := ConcreteWeylBenchmark.matter_nonnegative
  mass := mass H
  generations := 1
  generations_ne := by norm_num
  charges := uniformCharges 0
  singlets := 0
  lightTarget := ConcreteWeylBenchmark.mass_hasDualSMTarget _

theorem actualSpectrum :
    AbelianActualSpectrum.spectrum (WeylZeroModeSupport.lightRepresentation (model H)) =
      WeylZeroModeSupport.lift
        (exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0) := by
  apply AbelianActualSpectrum.eval_injective
  intro g
  rw [AbelianActualSpectrum.spectrum_eval, WeylZeroModeSupport.eval_lift]
  exact radical_character H g

theorem lightSpectrum : WeylZeroModeSupport.lightSpectrum (model H) =
    exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0 := by
  ext key
  rw [WeylZeroModeSupport.lightSpectrum_apply, actualSpectrum]
  exact Finsupp.mapDomain_apply_of_injective keyMonoidHom_injective _ key

def continuousModel : ContinuousWeylModel.ContinuousWeylMassModel H :=
  ContinuousWeylMassTransport.ofStandard (model H)

theorem continuous_mass_heq : HEq (continuousModel H).mass (mass H) :=
  ContinuousWeylMassTransport.mass_heq (model H)

theorem continuous_mass_nonzero : (continuousModel H).mass.form ≠ 0 :=
  (ContinuousWeylMassTransport.mass_nonzero_iff (model H)).mpr (mass_nonzero H)

theorem continuous_radical_finrank :
    Module.finrank ℂ (continuousModel H).mass.radical.toSubmodule = 15 :=
  (ContinuousWeylMassTransport.radical_finrank (model H)).trans (radical_finrank H)

theorem continuous_lightSpectrum :
    PhysicalWeylZeroModeSupport.lightSpectrum (continuousModel H).toPhysical =
      exactSMWithSingletsResolvedCharacter 1 (uniformCharges (0 : ChargeLabel H)) 0 :=
  (ContinuousWeylMassTransport.lightSpectrum (model H)).trans (lightSpectrum H)

end

end GUT.StandardSMOrdinaryMass
