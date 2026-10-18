import GUT.Common.ProtonProtection.ConditionalInputChecks
import Physics.StandardModel.Operators.DgtFlavorRestriction

/-! Explicit X=3(B-L) action restriction. Light-spectrum origin is not assumed proved. -/
namespace GUT.BLResidualRestriction
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
open scoped TensorProduct
abbrev Residual := CyclicCharge.Group 6
abbrev Flavor := Fin 3 → ℂ

def embedding : Residual →* Circle where
  toFun g := ZMod.toCircle (Multiplicative.toAdd g)
  map_one' := by simp
  map_mul' _ _ := by simp [AddChar.map_add_eq_mul]

theorem embedding_injective : Function.Injective embedding := by
  intro g h he
  exact congrArg Multiplicative.ofAdd (ZMod.injective_toCircle he)

theorem embedding_pow_six (g : Residual) : embedding g ^ 6 = 1 := by
  change ZMod.toCircle (Multiplicative.toAdd g) ^ 6 = 1
  rw [← AddChar.map_nsmul_eq_pow]
  rw [nsmul_eq_mul]
  change ZMod.toCircle ((6 : ZMod 6) * Multiplicative.toAdd g) = 1
  rw [show (6 : ZMod 6) = 0 from by decide, zero_mul]
  exact ZMod.toCircle.map_zero_eq_one

theorem range_iff (z : Circle) : (∃ g, embedding g = z) ↔ z^6=1 := by
  constructor
  · rintro ⟨g,rfl⟩
    exact embedding_pow_six g
  · intro hz
    let r : rootsOfUnity 6 Circle := ⟨toUnits z, by
      rw [mem_rootsOfUnity']
      simpa using hz⟩
    obtain ⟨j,hj⟩ := (bijective_rootsOfUnityAddChar 6).surjective r
    refine ⟨Multiplicative.ofAdd j,?_⟩
    exact congrArg (fun u : rootsOfUnity 6 Circle => (u.val : Circle)) hj

/-- The stabilizer of a nonzero charge-six VEV is exactly the image. -/
theorem vev_stabilizer (z : Circle) (v : ℂ) (hv : v ≠ 0) :
    MixedChargeSelection.circleCharacter z 6 * v = v ↔ ∃ g, embedding g = z := by
  rw [range_iff]
  change (z : ℂ) ^ (6 : ℤ) * v = v ↔ _
  rw [zpow_ofNat]
  constructor
  · intro he
    apply Subtype.ext
    change (z : ℂ)^6 = 1
    exact (mul_right_cancel₀ hv (he.trans (one_mul v).symm))
  · intro he
    have hc := congrArg (fun w : Circle => (w : ℂ)) he
    simpa using congrArg (fun c : ℂ => c*v) hc

def charge (s : Species) : ℤ := baryon s - 3*lepton s

def uvFlavor (s : Species) : Representation ℂ Circle Flavor :=
  DgtFlavorRestriction.diagonal (fun _ => charge s)

/-- Standard three-generation q/l flavor input already used by the consumer. -/
abbrev residualFlavor := QLFiniteSupport.flavor (1 : ZMod 6) (-3)

theorem phase_restriction (g : Residual) (w : ℤ) :
    MixedChargeSelection.circleCharacter (embedding g) w =
      MixedChargeSelection.cyclicCharacter g (w : ZMod 6) := by
  change (ZMod.stdAddChar (Multiplicative.toAdd g)) ^ w = ZMod.stdAddChar ((w : ZMod 6)*_)
  simpa [zsmul_eq_mul] using ((ZMod.stdAddChar (N := 6)).map_zsmul_eq_zpow w
    (Multiplicative.toAdd g)).symm

/-- LR's charge-minus-six triplet VEV is fixed by the same subgroup. -/
theorem negative_vev_fixed (g : Residual) (v : ℂ) :
    MixedChargeSelection.circleCharacter (embedding g) (-6) * v = v := by
  rw [phase_restriction]
  rw [show ((-6 : ℤ) : ZMod 6) = 0 from by decide]
  simp [MixedChargeSelection.cyclicCharacter]

theorem charge_matches (s : Species) : (charge s : ZMod 6) =
    DuqlHiggsContent.signedCharge (1 : ZMod 6) (-3) s := by
  fin_cases s <;> decide +kernel

theorem flavor_restriction (s : Species) :
    (uvFlavor s).comp embedding = residualFlavor s := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  have he := DuqlHiggsContent.flavor_scalar (1 : ZMod 6) (-3) g s v
  ext i
  change MixedChargeSelection.circleCharacter (embedding g) (charge s) * v i = _
  rw [phase_restriction,charge_matches]
  exact congrArg (fun w : Flavor => w i) he.symm

theorem actual_field_restriction (s : Species)
    (k : StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) (g : Residual)
    (v : DeltaLOneSignedFields.Field (F := fun _ => Flavor) s) :
    DeltaLOneSignedFields.field residualFlavor s (k,g) v =
      DeltaLOneSignedFields.field uvFlavor s (k,embedding g) v := by
  have hf : residualFlavor s g = uvFlavor s (embedding g) :=
    (congrArg (fun r : Representation ℂ Residual Flavor => r g) (flavor_restriction s)).symm
  have he : DeltaLOneSignedFields.field residualFlavor s (k,g) =
      DeltaLOneSignedFields.field uvFlavor s (k,embedding g) := by
    apply TensorProduct.ext'
    intro x y
    simp only [DeltaLOneSignedFields.field, ExternalInvariantTensor.external,
      Representation.tprod_apply, TensorProduct.map_tmul]
    change DeltaLOneSignedFields.localField s k x ⊗ₜ[ℂ] residualFlavor s g y =
      DeltaLOneSignedFields.localField s k x ⊗ₜ[ℂ] uvFlavor s (embedding g) y
    rw [hf]
  exact LinearMap.congr_fun he v

theorem charge_conjugates (i : Fin 5) :
    charge ⟨i.val+5,by omega⟩ = -charge ⟨i.val,by omega⟩ := by
  fin_cases i <;> decide +kernel

def uvHiggsFlavor (_s : BnvMixedInput.ScalarSpecies) : Representation ℂ Circle ℂ :=
  Representation.trivial ℂ Circle ℂ

def residualHiggsFlavor (_s : BnvMixedInput.ScalarSpecies) : Representation ℂ Residual ℂ :=
  Representation.trivial ℂ Residual ℂ

theorem actual_higgs_restriction (s : BnvMixedInput.ScalarSpecies)
    (k : StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) (g : Residual)
    (v : BnvMixedInput.ScalarField (S := fun _ => ℂ) s) :
    BnvMixedInput.scalarField residualHiggsFlavor s (k,g) v =
      BnvMixedInput.scalarField uvHiggsFlavor s (k,embedding g) v := rfl

/-- A neutral Higgs flavor action restricts to the same neutral action. -/
theorem higgs_restriction :
    (Representation.trivial ℂ Circle ℂ).comp embedding =
      Representation.trivial ℂ Residual ℂ := rfl

/-- All-degree attainment now stated on the restricted continuous action itself. -/
theorem restricted_b1_attained : ∃ (n : ℕ) (p : Fin n → Species) (h d : ℕ),
    (SMQLPatternRequests.blCharge p).1.natAbs = 3 ∧
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (fun s => (uvFlavor s).comp embedding) p h d) ∧
    SMChargeDegreeBounds.twiceDimension n h d = 12 := by
  have hf : (fun s => (uvFlavor s).comp embedding) = residualFlavor :=
    funext flavor_restriction
  rw [hf]
  exact ConditionalInputChecks.matter_parity_b1_minimum.attained

theorem restricted_b1_lower {n : ℕ} (p : Fin n → Species) (h d : ℕ)
    (hb : (SMQLPatternRequests.blCharge p).1.natAbs = 3)
    (ha : SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace
      (fun s => (uvFlavor s).comp embedding) p h d)) :
    12 ≤ SMChargeDegreeBounds.twiceDimension n h d := by
  have hf : (fun s => (uvFlavor s).comp embedding) = residualFlavor :=
    funext flavor_restriction
  rw [hf] at ha
  exact ConditionalInputChecks.matter_parity_b1_minimum.lower n p h d hb ha

end
end GUT.BLResidualRestriction
