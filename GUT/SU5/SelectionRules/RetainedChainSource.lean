import GUT.SU5.SelectionRules.ChargeProfiles
import GUT.Common.StandardChain.StandardChain
import GUT.SU5.Branching.ProfileEvaluation
import Math.RepresentationTheory.Multiplicity.ExplicitMultiplicityTrace

open Math

/-! Actual product-group action on the existing retained generation model.
The residual centralizer action is retained, including generation mixing;
no replacement by scalar characters on the original field space is assumed. -/

set_option autoImplicit false

namespace GUT.SU5.RetainedChainSource

noncomputable section

open MatterSource ResidualSectors StandardModelEmbedding
open FiniteAbelianChargeSectors ProfileEvaluation

variable {H : Type*} [CommGroup H] {n : ℕ} (R : OrdinaryAction H n)

def residual : Representation ℂ H (Space n) where
  toFun h := (R h).val.val.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro x
    change (R 1).val.val x = x
    rw [R.map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change (R (g * h)).val.val x = (R g).val.val ((R h).val.val x)
    rw [R.map_mul]
    rfl

theorem residual_commutes (g : TargetGroup) (h : H) :
    Commute (gauge n g) (residual R h) := by
  apply LinearMap.ext
  intro x
  exact (congrArg (fun f : Space n →L[ℂ] Space n => f x) ((R h).property g).eq).symm

def joint : Representation ℂ (TargetGroup × H) (Space n) :=
  CommutingUnitaryActions.combined (gauge n) (residual R) (residual_commutes R)

theorem joint_restrict_gauge : (joint R).comp (MonoidHom.inl TargetGroup H) = gauge n :=
  CommutingUnitaryActions.combined_restrict_left _ _ _

theorem joint_restrict_residual : (joint R).comp (MonoidHom.inr TargetGroup H) = residual R :=
  CommutingUnitaryActions.combined_restrict_right _ _ _

theorem residual_unitary : UnitaryMultiplicity.IsUnitaryRepresentation (residual R) :=
  fun h => ContinuousLinearMap.inner_map_map_of_mem_unitary (R h).val.property

theorem joint_unitary : UnitaryMultiplicity.IsUnitaryRepresentation (joint R) :=
  CommutingUnitaryActions.combined_unitary _ _ _ (gauge_unitary n) (residual_unitary R)

theorem joint_apply (g : TargetGroup × H) (x : Space n) (i : Kind) (a : Fin n) :
    joint R g x i a = ∑ b, (sectorAction R i g.2).val a b • constituent i g.1 (x i b) := by
  change constituent i g.1 ((R g.2).val.val x i a) = _
  rw [action_eq_multiplicity]
  simp only [map_sum, map_smul]

theorem joint_eq_mix_action (g : TargetGroup × H) :
    joint R g = HilbertMultiplicityOperator.mix (fun _ : Kind => n) Carrier
      (fun i => (sectorAction R i g.2).val) * gauge n g.1 := by
  apply LinearMap.ext
  intro x
  ext i a
  exact joint_apply R g x i a

theorem joint_character (g : TargetGroup × H) :
    (joint R).character g = ∑ i : Kind,
      (sectorAction R i g.2).val.trace * (constituent i).character g.1 := by
  unfold Representation.character
  rw [joint_eq_mix_action]
  exact ExplicitMultiplicity.trace_mix_action _ _ _ _ _

theorem generation_character (i : Kind) (h : H) :
    (representation R i).character h = (sectorAction R i h).val.trace := by
  let e := (EuclideanSpace.equiv (Fin n) ℂ).toLinearEquiv
  have he : e.conj (representation R i h) = Matrix.toLin' (sectorAction R i h).val := by
    apply LinearMap.ext
    intro x
    rfl
  rw [Representation.character, ← LinearMap.trace_conj' _ e, he, Matrix.trace_toLin'_eq]

theorem kindProfile_eval (i : Kind) (h : H) :
    profileEval (ChargeProfiles.kindProfile R i) h = (sectorAction R i h).val.trace := by
  rw [← generation_character]
  unfold profileEval ChargeProfiles.kindProfile
  rw [Finsupp.sum_mapDomain_index]
  · exact UnitaryCharacterSpectrum.profile_eval (representation R i) (representation_unitary R i) h
  · simp
  · intros; simp [add_mul]

theorem torus_character (g : TorusCharacter.CombinedGroup H) :
    (TorusCharacterSource.restrict (joint R)).character g =
      TorusCharacter.eval (FiniteChargeProfiles.target (ChargeProfiles.profiles R)) g := by
  change (joint R).character (MaximalTorus.hom g.1, g.2) = _
  rw [joint_character]
  change _ = TorusCharacter.eval (FiniteChargeProfiles.target
    (StandardAbelianCharge.sectorCharges (ChargeProfiles.kindProfile R .ten)
      (ChargeProfiles.kindProfile R .barFive))) g
  rw [eval_block_target, kindProfile_eval, kindProfile_eval]
  change (∑ i ∈ ({.ten, .barFive} : Finset Kind),
    (sectorAction R i g.2).val.trace * (constituent i).character (MaximalTorus.hom g.1)) = _
  simp [constituent, mul_comm]
  rfl

open InvariantWeylMass TorusCharacterSource
open StandardWeylDualTarget FiniteChargeProfiles

/-- The old source determines the dual target for every invariant mass;
no light-profile compatibility is postulated in this adapter. -/
theorem hasTarget (B : SymmetricMass (restrict (joint R))) :
    TorusMassSource.HasTarget (joint R) B (ChargeProfiles.profiles R) 0 := by
  intro g
  rw [B.radical_dual_character_eq, Representation.char_dual,
    torus_character, torus_character]
  simp [targetWithSinglets, TorusCharacter.eval_chiralDifference,
    StandardSMCharacterTarget.singletResolvedCharacter]

def massModel (hn : 0 < n) (B : SymmetricMass (restrict (joint R))) :
    StandardChain.Model (MonoidHom.id TargetGroup) (joint R) :=
  .ofSU5 (joint R) (joint_unitary R) B (ChargeProfiles.family R hn) 0 (hasTarget R B)

@[simp] theorem massModel_mass (hn : 0 < n) (B : SymmetricMass (restrict (joint R))) :
    (massModel R hn B).mass = B := rfl

/-- The legacy retained model keeps every generation, so its faithful
mass-sector realization has zero mass. -/
def model (hn : 0 < n) : StandardChain.Model (MonoidHom.id TargetGroup) (joint R) :=
  massModel R hn (SymmetricMass.zero (restrict (joint R)))

theorem zero_radical_character (g : TorusCharacter.CombinedGroup H) :
    (SymmetricMass.zero (restrict (joint R))).radical.toRepresentation.character g =
      TorusCharacter.eval (target (ChargeProfiles.profiles R)) g := by
  rw [Representation.char_iso (SymmetricMass.zeroRadicalEquiv (restrict (joint R)))]
  exact torus_character R g

theorem zero_radical_spectrum :
    AbelianMassSpectrum.radicalSpectrum (SymmetricMass.zero (restrict (joint R)))
        (TorusMassSource.restricted_unitary (joint R) (joint_unitary R)) =
      TorusCharacter.lift (target (ChargeProfiles.profiles R)) := by
  apply AbelianActualSpectrum.eval_injective
  intro g
  rw [AbelianMassSpectrum.radicalSpectrum_eval, TorusCharacter.eval_lift]
  exact zero_radical_character R g

/-- Exact full-spectrum compatibility, stronger than equality of the dual
index, for the retained-field specialization. -/
theorem retained_spectrum :
    TorusMassSource.spectrum (joint R) (joint_unitary R)
        (SymmetricMass.zero (restrict (joint R))) = target (ChargeProfiles.profiles R) := by
  ext key
  simp only [TorusMassSource.spectrum, Finsupp.comapDomain_apply, zero_radical_spectrum,
    TorusCharacter.lift,
    Finsupp.mapDomain_apply_of_injective TorusCharacter.keyCharacter_injective]

theorem spectrum_eq (hn : 0 < n) :
    (model R hn).lightSpectrum = target (ChargeProfiles.profiles R) := retained_spectrum R

theorem selection_rule_obstruction (hn : 0 < n) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (target (ChargeProfiles.profiles R)) := by
  rw [← spectrum_eq R hn]
  exact (model R hn).selection_rule_obstruction

section Continuity

variable [TopologicalSpace H]

theorem joint_continuous (hR : Continuous R) :
    Continuous (fun p : (TargetGroup × H) × Space n => joint R p.1 p.2) := by
  apply CommutingUnitaryActions.combined_jointlyContinuous
  · exact gauge_jointlyContinuous n
  · exact ((continuous_subtype_val.comp (continuous_subtype_val.comp hR)).comp
      continuous_fst).clm_apply continuous_snd

variable [IsTopologicalGroup H]

def continuousMassModel (hR : Continuous R) (hn : 0 < n)
    (B : SymmetricMass (restrict (joint R))) :
    StandardChain.ContinuousModel (MonoidHom.id TargetGroup) (joint R) where
  toModel := massModel R hn B
  inclusion_injective := Function.injective_id
  inclusion_continuous := continuous_id
  action_continuous := joint_continuous R hR

def continuousModel (hR : Continuous R) (hn : 0 < n) :
    StandardChain.ContinuousModel (MonoidHom.id TargetGroup) (joint R) :=
  continuousMassModel R hR hn (SymmetricMass.zero (restrict (joint R)))

omit [IsTopologicalGroup H] in
theorem continuousModel_toModel (hR : Continuous R) (hn : 0 < n) :
    (continuousModel R hR hn).toModel = model R hn := rfl

end Continuity

end

end GUT.SU5.RetainedChainSource
