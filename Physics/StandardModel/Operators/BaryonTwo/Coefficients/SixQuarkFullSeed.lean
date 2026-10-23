import Physics.StandardModel.Operators.Higgs.OutsideFamilyHiggsTrials
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTwoCoordinates

namespace Physics.SixQuarkFullSeed
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput SixQuarkInvariant
open scoped TensorProduct BigOperators
variable {k : ℕ} [NeZero k] (q l : ZMod k)

abbrev Fields := ∀ u : Species, DeltaLOneSignedFields.Field
  (F := fun u => FlavoredCyclicSelection.signedIndex (fun _ : Fin 5 => Fin 3) u → ℂ) u

def strip : (Quark ⊗[ℂ] (Fin 3 → ℂ)) →ₗ[ℂ] Quark :=
  (TensorProduct.rid ℂ Quark).toLinearMap.comp
    (TensorProduct.map LinearMap.id (LinearMap.proj 0))

@[simp] theorem strip_tmul (v : Quark) (w : Fin 3 → ℂ) : strip (v ⊗ₜ[ℂ] w) = w 0 • v := by
  simp [strip]

def projection : Fields →ₗ[ℂ] Quark × Quark :=
  (strip.comp (LinearMap.proj (1 : Species))).prod (strip.comp (LinearMap.proj (2 : Species)))

def inclusion : (Quark × Quark) →ₗ[ℂ] Fields :=
  (LinearMap.single ℂ _ 1).comp
    (((TensorProduct.mk ℂ Quark (Fin 3 → ℂ)).flip (fun _ => 1)).comp (LinearMap.fst ℂ Quark Quark)) +
  (LinearMap.single ℂ _ 2).comp
    (((TensorProduct.mk ℂ Quark (Fin 3 → ℂ)).flip (fun _ => 1)).comp (LinearMap.snd ℂ Quark Quark))

theorem projection_inclusion (x : Quark × Quark) : projection (inclusion x) = x := by
  ext <;> simp [projection,inclusion]

theorem strip_up_action
    (g : (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × CyclicCharge.Group k)
    (v : Quark ⊗[ℂ] (Fin 3 → ℂ)) :
    strip (DeltaLOneSignedFields.field (ContentHiggsSupport.flavor q l) 1 g v) =
      MixedChargeSelection.cyclicCharacter g.2 q • DeltaBTwoSixQuark.upField g.1 (strip v) := by
  induction v using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb,smul_add]
  | tmul v w =>
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,ha,hb,smul_add]
    | tmul c s =>
      simp [DeltaLOneSignedFields.field, ExternalInvariantTensor.external,
        Representation.tprod_apply, ContentHiggsSupport.flavor,
        DuqlHiggsContent.fermionFlavor, DressedDuqlFamily.flavor,
        FlavoredCyclicSelection.flavor, FlavoredCyclicSelection.signedCharge,
        FlavoredCyclicSelection.slot, InverseCyclicSMCharges.universal,
        InverseCyclicSMCharges.physical, CyclicWeightCoordinates.diagonal_apply,
        DeltaLOneSignedFields.localField, DeltaLOneSignedFields.gauge, DeltaLOneSignedFields.rightHanded,
        DeltaBTwoSixQuark.upField, FourSameWeylCompleteness.action,
        MixedChargeSelection.cyclicCharacter, smul_smul, mul_comm]

theorem strip_down_action
    (g : (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × CyclicCharge.Group k)
    (v : Quark ⊗[ℂ] (Fin 3 → ℂ)) :
    strip (DeltaLOneSignedFields.field (ContentHiggsSupport.flavor q l) 2 g v) =
      MixedChargeSelection.cyclicCharacter g.2 q • DeltaBTwoSixQuark.downField g.1 (strip v) := by
  induction v using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add,ha,hb,smul_add]
  | tmul v w =>
    induction v using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,ha,hb,smul_add]
    | tmul c s =>
      simp [DeltaLOneSignedFields.field, ExternalInvariantTensor.external,
        Representation.tprod_apply, ContentHiggsSupport.flavor,
        DuqlHiggsContent.fermionFlavor, DressedDuqlFamily.flavor,
        FlavoredCyclicSelection.flavor, FlavoredCyclicSelection.signedCharge,
        FlavoredCyclicSelection.slot, InverseCyclicSMCharges.universal,
        InverseCyclicSMCharges.physical, CyclicWeightCoordinates.diagonal_apply,
        DeltaLOneSignedFields.localField, DeltaLOneSignedFields.gauge, DeltaLOneSignedFields.rightHanded,
        DeltaBTwoSixQuark.downField, FourSameWeylCompleteness.action,
        MixedChargeSelection.cyclicCharacter, smul_smul, mul_comm]



theorem projection_action
    (g : (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × CyclicCharge.Group k) (x : Fields) :
    projection (DeltaLOneSignedFields.fullRepresentation (ContentHiggsSupport.flavor q l) g x) =
      MixedChargeSelection.cyclicCharacter g.2 q •
        SixSlotAlternation.action DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField g.1 (projection x) := by
  apply Prod.ext
  · exact strip_up_action q l g (x 1)
  · exact strip_down_action q l g (x 2)

def localSeed : SixQuarkTwoCoordinates.Sector := SixQuarkTwoCoordinates.twoCoordinateEquiv.symm (fun _ => 1)

theorem localSeed_nonzero : localSeed ≠ 0 := by
  intro hz
  have hh := congrArg (fun f => SixQuarkTwoCoordinates.twoCoordinateEquiv f 0) hz
  simp [localSeed, LinearEquiv.map_zero] at hh

theorem phase_six (hc : 6*q=0) (g : CyclicCharge.Group k) :
    MixedChargeSelection.cyclicCharacter g q ^ 6 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]
  simpa [nsmul_eq_mul] using congrArg (MixedChargeSelection.cyclicCharacter g) hc

def raw (hc : 6*q=0) : FiniteSpeciesExterior.Coefficient
    (DeltaLOneSignedFields.field (ContentHiggsSupport.flavor q l)) 6 where
  toLinearMap := localSeed.val.toLinearMap.comp (exteriorPower.map 6 projection)
  isIntertwining' g := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change localSeed.val (exteriorPower.map 6 projection
      ((DeltaLOneSignedFields.fullRepresentation (ContentHiggsSupport.flavor q l)).exteriorPower 6 g
        (exteriorPower.ιMulti ℂ 6 v))) = localSeed.val (exteriorPower.map 6 projection (exteriorPower.ιMulti ℂ 6 v))
    rw [Representation.exteriorPower_apply_ιMulti, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti]
    simp only [Function.comp_def]
    simp_rw [projection_action]
    have hm := (localSeed.val.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ 6)).toMultilinearMap.map_smul_univ
      (fun _ : Fin 6 => MixedChargeSelection.cyclicCharacter g.2 q)
      (fun i => SixSlotAlternation.action DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField g.1 (projection (v i)))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
    rw [phase_six q hc g.2, one_smul] at hm
    change localSeed.val (exteriorPower.ιMulti ℂ 6 (fun i =>
      MixedChargeSelection.cyclicCharacter g.2 q •
      SixSlotAlternation.action DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField g.1 (projection (v i)))) =
      localSeed.val (exteriorPower.ιMulti ℂ 6 (fun i =>
        SixSlotAlternation.action DeltaBTwoSixQuark.upField DeltaBTwoSixQuark.downField g.1 (projection (v i)))) at hm
    rw [hm]
    have he := IntertwiningMap.isIntertwining _ _ localSeed.val g.1 (exteriorPower.ιMulti ℂ 6 (fun i => projection (v i)))
    rw [Representation.exteriorPower_apply_ιMulti] at he
    exact he

theorem raw_nonzero (hc : 6*q=0) : raw q l hc ≠ 0 := by
  intro hh
  apply localSeed_nonzero
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have he := congrArg (fun f => f (exteriorPower.ιMulti ℂ 6 (fun i => inclusion (v i)))) hh
  simpa [raw, exteriorPower.map_apply_ιMulti, projection_inclusion, Function.comp_def] using he


theorem projection_single_zero (u : Species) (h1 : u≠1) (h2 : u≠2)
    (v : DeltaLOneSignedFields.Field
      (F := fun u => FlavoredCyclicSelection.signedIndex (fun _ : Fin 5 => Fin 3) u → ℂ) u) :
    projection (Pi.single u v) = 0 := by
  ext <;> simp [projection, Pi.single_eq_of_ne (Ne.symm h1), Pi.single_eq_of_ne (Ne.symm h2)]

theorem support_of_nonzero (hc : 6*q=0) (p : Fin 6 → Species)
    (v : ∀ i, DeltaLOneSignedFields.Field
      (F := fun u => FlavoredCyclicSelection.signedIndex (fun _ : Fin 5 => Fin 3) u → ℂ) (p i))
    (hn : FiniteSpeciesExterior.restrict (DeltaLOneSignedFields.field (ContentHiggsSupport.flavor q l))
      (raw q l hc) p v ≠ 0) : OutsideFamilyHiggsTrials.sixQuarks p := by
  have hs : ∀ i, p i=1 ∨ p i=2 := by
    intro i
    by_contra hi
    push Not at hi
    apply hn
    change localSeed.val (exteriorPower.map 6 projection (exteriorPower.ιMulti ℂ 6
      (fun j => Pi.single (p j) (v j)))) = 0
    rw [exteriorPower.map_apply_ιMulti]
    exact (localSeed.val.toLinearMap.compAlternatingMap (exteriorPower.ιMulti ℂ 6)).toMultilinearMap.map_coord_zero i
      (projection_single_zero (p i) hi.1 hi.2 (v i))
  have hy := ExteriorWeightSupport.circle_constraint
    (FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field (ContentHiggsSupport.flavor q l)))
    (raw q l hc) (fun i => Pi.single (p i) (v i)) (fun i => hypercharge (p i))
    DeltaLOneSignedFields.fullHypercharge
    (by intro z i; rw [FiniteSpeciesExterior.action_single, DeltaLOneSignedFields.field_hypercharge]; exact Pi.single_smul _ _ _)
    hn
  have hY : (∑ i, hypercharge (p i)) =
      6 * ((Finset.univ.filter (fun i => p i=1)).card : ℤ) - 12 := by
    calc
      _ = ∑ i, (6*(if p i=1 then (1 : ℤ) else 0)-2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases hs i with hh | hh <;> rw [hh] <;> norm_num [hypercharge]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp
  have hu : (Finset.univ.filter (fun i => p i=1)).card = 2 := by omega
  have hd : (Finset.univ.filter (fun i => p i=2)).card = 4 := by
    have hp : (Finset.univ.filter (fun i => p i=1)).card +
      (Finset.univ.filter (fun i => p i=2)).card = 6 := by
      calc
        _ = (∑ i, if p i=1 then (1 : ℕ) else 0) + (∑ i, if p i=2 then (1 : ℕ) else 0) := by simp
        _ = ∑ i, ((if p i=1 then (1 : ℕ) else 0)+(if p i=2 then 1 else 0)) := Finset.sum_add_distrib.symm
        _ = ∑ _ : Fin 6, (1 : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rcases hs i with hh | hh <;> simp [hh]
        _ = 6 := by simp
    omega
  apply FiniteSpeciesExterior.permutation_of_counts
  intro u
  have canonical : (Finset.univ.filter (fun i => OutsideFamilyHiggsTrials.sixPattern i=u)).card =
      if u=1 then 2 else if u=2 then 4 else 0 := by fin_cases u <;> decide +kernel
  rw [canonical]
  by_cases h1 : u=1
  · subst u; simp only [ite_true]; exact hu
  · rw [ite_eq_right h1]
    by_cases h2 : u=2
    · subst u; simp only [ite_true]; exact hd
    · rw [ite_eq_right h2]
      have hz : Finset.univ.filter (fun i => p i=u) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro i hi
        rcases hs i with hh | hh <;> rw [hh] <;> exact Ne.symm (by assumption)
      rw [hz]; rfl

def seed (hc : 6*q=0) : ContentHiggsSupport.SeedSpace q l OutsideFamilyHiggsTrials.sixQuarks :=
  ⟨raw q l hc, by
    intro p hp
    ext v
    by_contra hn
    exact hp (support_of_nonzero q l hc p v hn)⟩

theorem seed_nonzero (hc : 6*q=0) : seed q l hc ≠ 0 := by
  intro hz
  exact raw_nonzero q l hc (congrArg Subtype.val hz)

theorem seed_exists (hc : 6*q=0) :
    SelectionCriteria.Allowed (ContentHiggsSupport.SeedSpace q l OutsideFamilyHiggsTrials.sixQuarks) :=
  ⟨seed q l hc, seed_nonzero q l hc⟩

theorem allowed_iff (h a : ℕ) :
    SelectionCriteria.Allowed (ContentHiggsSupport.Space q l OutsideFamilyHiggsTrials.sixQuarks h a) ↔
      h=a ∧ 6*q=0 := OutsideFamilyHiggsTrials.six_iff_of_seed q l (seed_exists q l) h a


theorem forbidden_iff (h a : ℕ) :
    SelectionCriteria.Forbidden (ContentHiggsSupport.Space q l OutsideFamilyHiggsTrials.sixQuarks h a) ↔
      h≠a ∨ 6*q≠0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, allowed_iff]
  exact not_and_or

theorem all_forbidden_iff :
    (∀ h a, SelectionCriteria.Forbidden (ContentHiggsSupport.Space q l OutsideFamilyHiggsTrials.sixQuarks h a)) ↔
      6*q≠0 := ContentHiggsSupport.all_forbidden_iff q l OutsideFamilyHiggsTrials.sixQuarks (6*q)
        (OutsideFamilyHiggsTrials.six_weight q l) OutsideFamilyHiggsTrials.six_hyper (seed_exists q l)

end
end Physics.SixQuarkFullSeed
