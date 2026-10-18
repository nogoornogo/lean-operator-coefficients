import Physics.StandardModel.Spectrum.LeptonTrialitySource
import Physics.StandardModel.Spectrum.GaugeTorusTrace
import Physics.StandardModel.Spectrum.ProfileChiralIndex
import Physics.FieldTheory.Mass.AbelianMassSpectrum

open Math

/-! Identify the actual SM triality mass radical with the finite supported
counterexample. Determinant-one coordinates are only a weight convention;
no action of a UV unification group or Weyl-invariance assumption is used. -/

set_option autoImplicit false
open scoped BigOperators

namespace GUT.LeptonTrialitySpectrum
noncomputable section

open SU5 SU5.TorusMatterCharacter StandardSMGaugeTensor
open StandardAbelianCharge StandardSMCharacterTarget FiniteAbelianChargeSectors
open FiniteChargeProfiles InvariantWeylMass StandardWeylDualTarget
open LeptonTriality LeptonTrialitySource

abbrev PhysicalGroup := PhysicalTorus.Coordinates × Residual

def inclusion : PhysicalGroup →* LeptonTrialitySource.Group :=
  PhysicalTorus.gaugeHom.prodMap (MonoidHom.id Residual)

def coordinateMap : PhysicalGroup →* TorusCharacter.CombinedGroup Residual :=
  PhysicalTorus.toTorus.prodMap (MonoidHom.id Residual)

def keyCharacter (key : ResolvedKey (ChargeLabel Residual)) : PhysicalGroup →* ℂ :=
  (TorusCharacter.keyCharacter key).comp coordinateMap

theorem keyCharacter_injective : Function.Injective keyCharacter := by
  intro a b he
  apply TorusCharacter.keyCharacter_injective
  ext g
  obtain ⟨z, hz⟩ := PhysicalTorus.toTorus_surjective g.1
  have h := congrArg (fun f : PhysicalGroup →* ℂ => f (z, g.2)) he
  simpa [keyCharacter, coordinateMap, hz] using h

def lift (p : ResolvedCharacter (ChargeLabel Residual)) :
    AbelianActualSpectrum.Polynomial PhysicalGroup := Finsupp.mapDomain keyCharacter p

theorem eval_lift (p : ResolvedCharacter (ChargeLabel Residual)) (g : PhysicalGroup) :
    AbelianActualSpectrum.eval (lift p) g = TorusCharacter.eval p (coordinateMap g) := by
  unfold lift AbelianActualSpectrum.eval
  rw [Finsupp.sum_mapDomain_index]
  · rfl
  · simp
  · intros; simp [add_mul]

theorem eval_target_sum (t : MaximalTorus.Torus) (h : Residual) :
    TorusCharacter.eval LeptonTriality.spectrum (t, h) =
      ∑ i : Fin 15, (3 : ℂ) *
        (TorusCharacter.weightCharacter (smReducedWeight i) t : ℂ) *
        ((smCharge assignment i).toMul h : ℂ) := by
  change TorusCharacter.eval (target (FiniteChargeProfiles.pure 3 assignment)) (t, h) = _
  rw [target_pure, ← TorusCharacter.evalAddHom_apply, exactSMResolvedCharacter, map_sum]
  simp [TorusCharacter.evalAddHom_apply, TorusCharacter.eval_single, smResolvedKey,
    TorusCharacter.keyCharacter_apply, mul_assoc]

theorem trace_target (z : PhysicalTorus.Coordinates) (h : Residual) :
    3 * generationTrace (PhysicalTorus.gaugePoint z, h) =
      TorusCharacter.eval LeptonTriality.spectrum (PhysicalTorus.toTorus z, h) := by
  rw [eval_target_sum]
  unfold generationTrace
  simp only [quark, upRight, downRight, lepton, electronRight, character_twist,
    Representation.char_tensor, Pi.mul_apply]
  rw [color_character, color_character_inv, weak_character]
  have ht (g : GaugeGroup) : (Representation.trivial ℂ GaugeGroup ℂ).character g = 1 := by
    change LinearMap.trace ℂ ℂ LinearMap.id = 1
    simp
  rw [ht]
  simp_rw [PhysicalTorus.weightCharacter_toTorus]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, smReducedWeight, smCharge,
    assignment, charges, label, PhysicalTorus.exponent, phase, PhysicalTorus.gaugePoint]
  have hc : (Circle.coeHom : Circle → ℂ) = (fun a : Circle => (a : ℂ)) := rfl
  simp only [hc]
  field_simp
  ring

def restricted : Representation ℂ PhysicalGroup HilbertMatter := rho.comp inclusion

theorem restricted_unitary : UnitaryMultiplicity.IsUnitaryRepresentation restricted :=
  fun g v w => model_unitary.inner_map_map (inclusion g) v w

def restrictedMass : SymmetricMass restricted := mass.restrict inclusion

theorem restrictedMass_eq_zero : restrictedMass = SymmetricMass.zero restricted := rfl

theorem radical_trace (g : PhysicalGroup) :
    restrictedMass.radical.toRepresentation.character g =
      TorusCharacter.eval LeptonTriality.spectrum (coordinateMap g) := by
  rw [restrictedMass_eq_zero, Representation.char_iso (SymmetricMass.zeroRadicalEquiv restricted)]
  change unitaryModel.toRepresentation.character (inclusion g) = _
  rw [← Representation.char_iso modelEquiv, matter_character]
  exact trace_target g.1 g.2

theorem full_spectrum_eq :
    AbelianMassSpectrum.radicalSpectrum restrictedMass restricted_unitary =
      lift LeptonTriality.spectrum := by
  apply AbelianActualSpectrum.eval_injective
  intro g
  rw [AbelianMassSpectrum.radicalSpectrum_eval, eval_lift, radical_trace]

/-- Actual joint torus/residual eigenspace multiplicities, not a supplied target. -/
def actualSpectrum : ResolvedCharacter (ChargeLabel Residual) :=
  Finsupp.comapDomain keyCharacter
    (AbelianMassSpectrum.radicalSpectrum restrictedMass restricted_unitary)
    keyCharacter_injective.injOn

theorem actualSpectrum_eq : actualSpectrum = LeptonTriality.spectrum := by
  ext key
  simp only [actualSpectrum, Finsupp.comapDomain_apply, full_spectrum_eq, lift,
    Finsupp.mapDomain_apply_of_injective keyCharacter_injective]

theorem actual_chiral_index :
    chiralDifference actualSpectrum = chiralDifference (target family.profiles) := by
  rw [actualSpectrum_eq]
  rfl

theorem radical_dual_trace (g : PhysicalGroup) :
    restrictedMass.radical.toRepresentation.character g -
        restrictedMass.radical.toRepresentation.dual.character g =
      TorusCharacter.eval (chiralDifference (target family.profiles)) (coordinateMap g) := by
  rw [Representation.char_dual, radical_trace, radical_trace,
    TorusCharacter.eval_chiralDifference, map_inv]
  rfl

theorem actual_forbids_all_supported :
    StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator actualSpectrum := by
  rw [actualSpectrum_eq]
  exact forbids_all_supported

theorem actual_supported : ChargesSupported actualSpectrum assignment := by
  rw [actualSpectrum_eq]
  exact assignment_supported

theorem actual_not_weylInvariant : ¬ ResolvedWeylInvariant actualSpectrum := by
  rw [actualSpectrum_eq]
  exact spectrum_not_weylInvariant

theorem exists_joint_zeroMode (i : Fin 15) :
    ∃ v : restrictedMass.radical.toSubmodule, v ≠ 0 ∧
      ∀ g, restrictedMass.radical.toRepresentation g v =
        keyCharacter (smResolvedKey assignment i) g • v := by
  apply UnitaryCharacterSpectrum.exists_eigenvector_of_coeff_ne_zero
    restrictedMass.radical.toRepresentation
    (AbelianMassSpectrum.radical_unitary restrictedMass restricted_unitary)
  change AbelianMassSpectrum.radicalSpectrum restrictedMass restricted_unitary
    (keyCharacter (smResolvedKey assignment i)) ≠ 0
  rw [full_spectrum_eq, lift, Finsupp.mapDomain_apply_of_injective keyCharacter_injective]
  change target (FiniteChargeProfiles.pure 3 assignment) (smReducedWeight i, smCharge assignment i) ≠ 0
  rw [target_apply_smReducedWeight]
  fin_cases i <;> simp [smCharge, FiniteChargeProfiles.pure]

/-- A concrete actual source satisfying the retained finite mass assumptions.
The spectrum equality includes all joint eigenspaces, not only a dual index.
The forbidden class is exactly the existing supported four-fermion predicate. -/
theorem actual_source_counterexample :
    Continuous (fun p : LeptonTrialitySource.Group × HilbertMatter => rho p.1 p.2) ∧
    UnitaryMultiplicity.IsUnitaryRepresentation rho ∧
    (∀ (g : GaugeGroup) (h : Residual) (v : HilbertMatter),
      rho (g, 1) (rho (1, h) v) = rho (1, h) (rho (g, 1) v)) ∧
    ∃ B : SymmetricMass rho, ∃ p : ResolvedCharacter (ChargeLabel Residual),
      Module.finrank ℂ B.radical.toSubmodule = 45 ∧
      AbelianMassSpectrum.radicalSpectrum (B.restrict inclusion) restricted_unitary = lift p ∧
      chiralDifference p = chiralDifference (target family.profiles) ∧
      ChargesSupported p assignment ∧
      StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator p := by
  refine ⟨model_jointlyContinuous, (fun g v w => model_unitary.inner_map_map g v w),
    gauge_residual_commute, mass, actualSpectrum, radical_finrank, ?_,
    actual_chiral_index, actual_supported, actual_forbids_all_supported⟩
  rw [actualSpectrum_eq]
  exact full_spectrum_eq

end
end GUT.LeptonTrialitySpectrum
