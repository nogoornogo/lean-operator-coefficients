import Physics.StandardModel.Operators.Higgs.NeutralHiggsPowers
import Physics.StandardModel.Operators.Selection.InverseCyclicSMCharges
import Physics.StandardModel.Operators.Selection.ComposableBLSupport

namespace Physics.DressedDuqlFamily
set_option autoImplicit false
noncomputable section
open Math Representation SelectionCriteria
variable {k : ℕ} [NeZero k] (q l : ZMod k)
abbrev Indices := FlavoredCyclicSelection.DuqlIndex (fun _ : Fin 5 => Fin 3)
  (InverseCyclicSMCharges.universal q l)
abbrev flavor := FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3)
  (InverseCyclicSMCharges.universal q l)

irreducible_def dictionary : DeltaLOneSignedFields.Sector (flavor q l) 1 ≃ₗ[ℂ]
    FlavoredCyclicSelection.Coordinates (fun _ : Fin 5 => Fin 3) (InverseCyclicSMCharges.universal q l) :=
  FlavoredCyclicSelection.equiv (fun _ : Fin 5 => Fin 3) (InverseCyclicSMCharges.universal q l)

/-- Only the actual DUQL coordinate factor is populated. -/
def seed : (Indices q l → ℂ) →ₗ[ℂ] DeltaLOneSignedFields.Sector (flavor q l) 1 where
  toFun c := (dictionary q l).symm (c,0,0,0)
  map_add' x y := by
    have h := (dictionary q l).symm.map_add (x,0,0,0) (y,0,0,0)
    simpa only [Prod.mk_add_mk,add_zero] using h
  map_smul' z x := by
    have h := (dictionary q l).symm.map_smul z (x,0,0,0)
    simpa only [Prod.smul_mk,smul_zero,RingHom.id_apply] using h

theorem seed_dictionary (c : Indices q l → ℂ) :
    dictionary q l (seed q l c) = (c,0,0,0) := by simp [seed]

theorem seed_injective : Function.Injective (seed q l) := by
  intro x y h
  have he := congrArg (fun f => (dictionary q l f).1) h
  simpa [seed] using he

def dress (r : ℕ) : (Indices q l → ℂ) →ₗ[ℂ]
    BnvMixedInput.Coefficient (flavor q l) (NeutralHiggsPowers.flavor (H := CyclicCharge.Group k)) 4 (r*2) :=
  (MixedInvariantDressing.productLinearRight (NeutralHiggsPowers.normalized (H := CyclicCharge.Group k) r)).comp
    ((DeltaLOneSignedInput.sector (DeltaLOneSignedFields.field (flavor q l)) 1).subtype.comp (seed q l))

/-- The actual mixed coefficient range, rather than a formal product expression. -/
abbrev Family (r : ℕ) := LinearMap.range (dress q l r)

theorem dress_nonzero (r : ℕ) (c : Indices q l → ℂ) (hc : c ≠ 0) : dress q l r c ≠ 0 := by
  apply MixedInvariantDressing.product_nonzero
  · intro h
    apply hc
    apply seed_injective q l
    apply Subtype.ext
    rw [map_zero]
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have he := congrArg (fun t => t x) h
    exact he
  · exact NeutralHiggsPowers.normalized_nonzero r

omit [NeZero k] in
theorem indices_nonempty_iff : Nonempty (Indices q l) ↔ 3*q+l=0 := by
  constructor
  · rintro ⟨p⟩
    have he := p.property
    simpa [FlavoredCyclicCoordinates.fourCharge,InverseCyclicSMCharges.universal,
      InverseCyclicSMCharges.physical,show (3 : ZMod k)*q=q+q+q by ring,add_assoc] using he
  · intro hz
    refine ⟨⟨((0,0),(0,0)),?_⟩⟩
    simp [FlavoredCyclicCoordinates.fourCharge,InverseCyclicSMCharges.universal,
      InverseCyclicSMCharges.physical]
    linear_combination hz

theorem allowed_iff (r : ℕ) : Allowed (Family q l r) ↔ 3*q+l=0 := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨c,hc⟩ := f.property
    have hn : Nonempty (Indices q l) := by
      by_contra h
      have : IsEmpty (Indices q l) := not_nonempty_iff.mp h
      have hz : c = 0 := by ext i; exact isEmptyElim i
      apply hf
      apply Subtype.ext
      rw [← hc,hz,map_zero]
      rfl
    exact (indices_nonempty_iff q l).mp hn
  · intro h
    obtain ⟨p⟩ := (indices_nonempty_iff q l).mpr h
    let c : Indices q l → ℂ := fun _ => 1
    have hc : c ≠ 0 := by intro hz; have he := congrFun hz p; norm_num [c] at he
    refine ⟨⟨dress q l r c,⟨c,rfl⟩⟩,?_⟩
    intro hz
    exact dress_nonzero q l r c hc (congrArg Subtype.val hz)

/-- Neutral DUQL content gives actual coefficients at arbitrarily large scalar degree. -/
theorem unbounded_allowance (h : 3*q+l=0) (bound : ℕ) :
    ∃ r, bound < r*2 ∧ Allowed (Family q l r) :=
  ⟨bound+1,by omega,(allowed_iff q l (bound+1)).mpr h⟩

/-- The certified DUQL ordering keeps its signed B/L grades under every scalar dressing. -/
theorem family_grades (r : ℕ) (s : Fin (r*2) → BnvMixedInput.ScalarSpecies) :
    MixedChargeSelection.charge ComposableBLSupport.fermionCharge ComposableBLSupport.bosonCharge
      (DeltaLOneFourFamilyDecomposition.pattern 0) s = (3,1) := by
  rw [ComposableBLSupport.charge_eq]
  decide +kernel

theorem forbidden_iff (r : ℕ) : Forbidden (Family q l r) ↔ 3*q+l ≠ 0 := by
  rw [forbidden_iff_not_allowed,allowed_iff]
end
end Physics.DressedDuqlFamily
