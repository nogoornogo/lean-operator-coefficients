import Physics.StandardModel.Operators.Higgs.FourFamilyHiggsContent
import Physics.StandardModel.Operators.Selection.AdmittedCyclicSMProhibition
import Physics.StandardModel.Operators.Selection.ThreeGenerationFermionBound

/-! Actual-carrier support adapter for arbitrary fermion content. Neutral
seed existence is explicit; the four-family consumers discharge it. -/
namespace Physics.ContentHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
open DuqlHiggsContent (scalarCount scalar_hypercharge scalarCount_total)
open scoped TensorProduct BigOperators
variable {k : ℕ} [NeZero k] (q l : ZMod k) {n : ℕ}

abbrev flavor := DuqlHiggsContent.fermionFlavor q l
abbrev scalar := DuqlHiggsContent.scalarFlavor (k := k)
abbrev charge := DuqlHiggsContent.signedCharge q l

def selected (P : (Fin n → Species) → Prop) (h a : ℕ)
    (p : Fin n → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies) : Prop :=
  P p ∧ scalarCount s 0 = h ∧ scalarCount s 1 = a


theorem selected_stable (P : (Fin n → Species) → Prop)
    (stable : ∀ p (e : Equiv.Perm (Fin n)), P (p ∘ e) ↔ P p)
    (h a : ℕ) (p : Fin n → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (e : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin (h+a))) :
    selected P h a (p ∘ e) (s ∘ f) ↔ selected P h a p s := by
  simp only [selected, stable, DuqlHiggsContent.scalarCount_perm]

abbrev Space (P : (Fin n → Species) → Prop) (h a : ℕ) :=
  MixedSpeciesProjection.supportSpace (selected P h a)
    (DeltaLOneSignedFields.field (flavor q l)) (BnvMixedInput.scalarField (scalar (k := k)))

def SeedSpace (P : (Fin n → Species) → Prop) : Submodule ℂ
    (FiniteSpeciesExterior.Coefficient (DeltaLOneSignedFields.field (flavor q l)) n) where
  carrier := {f | ∀ p, ¬ P p → FiniteSpeciesExterior.restrict
    (DeltaLOneSignedFields.field (flavor q l)) f p = 0}
  zero_mem' := by intro p hp; ext v; rfl
  add_mem' := by intro f g hf hg p hp; rw [FiniteSpeciesExterior.restrict_add, hf p hp, hg p hp, add_zero]
  smul_mem' := by intro z f hf p hp; rw [FiniteSpeciesExterior.restrict_smul, hf p hp, smul_zero]

variable (P : (Fin n → Species) → Prop) (Y : ℤ) (c : ZMod k)
  (hyper : ∀ p, P p → ∑ i, hypercharge (p i) = Y)
  (weight : ∀ p, P p → ∑ i, charge q l (p i) = c)

include hyper in
theorem hypercharge_of_nonzero (h a : ℕ) (f : Space q l P h a)
    (p : Fin n → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) (s j))
    (hn : BnvMixedInput.value (flavor q l) scalar f.val p s v w ≠ 0) :
    Y + 3*(h : ℤ) - 3*a = 0 := by
  have hs : selected P h a p s := by by_contra hs; exact hn (f.property p s hs v w)
  have hy := BnvMixedInput.hypercharge_of_nonzero (flavor q l) scalar f.val p s v w hn
  rw [hyper p hs.1, scalar_hypercharge, hs.2.1, hs.2.2] at hy
  omega

include weight in
theorem charge_of_nonzero (h a : ℕ) (f : Space q l P h a)
    (p : Fin n → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) (s j))
    (hn : BnvMixedInput.value (flavor q l) scalar f.val p s v w ≠ 0) : c = 0 := by
  have hs : selected P h a p s := by by_contra hs; exact hn (f.property p s hs v w)
  apply (CyclicCharge.neutral_iff c).mp
  intro g
  have he := MixedWeightSupport.scalar_constraint
    (FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field (flavor q l)))
    (FiniteSpeciesExterior.representation (BnvMixedInput.scalarField (scalar (k := k)))) f.val (1,g)
    (fun i => Pi.single (p i) (v i)) (fun j => Pi.single (s j) (w j))
    (fun i => MixedChargeSelection.cyclicCharacter g (charge q l (p i))) (fun _ => (1 : ℂ))
    (by intro i; rw [FiniteSpeciesExterior.action_single, DuqlHiggsContent.field_scalar]; exact Pi.single_smul _ _ _)
    (by intro j; rw [FiniteSpeciesExterior.action_single, DuqlHiggsContent.boson_scalar]; simp)
  simp only [Finset.prod_const_one, mul_one] at he
  have hh := MixedChargeSelection.total_eq_character (MixedChargeSelection.cyclicCharacter g)
    (charge q l) (fun _ : BnvMixedInput.ScalarSpecies => (0 : ZMod k)) p s
  simp only [MixedScalarSelection.total, AddChar.map_zero_eq_one, Finset.prod_const_one, mul_one,
    MixedChargeSelection.charge, Finset.sum_const_zero, add_zero] at hh
  rw [hh, weight p hs.1] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hn)

theorem exists_value (h a : ℕ) (f : Space q l P h a) (hf : f ≠ 0) :
    ∃ p s v w, BnvMixedInput.value (flavor q l) scalar f.val p s v w ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hf
  apply Subtype.ext
  apply BnvMixedInput.value_ext (flavor q l) scalar
  intro p s v w
  exact hn p s v w

include hyper weight in
theorem necessary (h a : ℕ) (hf : SelectionCriteria.Allowed (Space q l P h a)) :
    Y + 3*(h : ℤ) - 3*a = 0 ∧ c = 0 := by
  obtain ⟨f,hf⟩ := hf
  obtain ⟨p,s,v,w,hn⟩ := exists_value q l P h a f hf
  exact ⟨hypercharge_of_nonzero q l P Y hyper h a f p s v w hn,
    charge_of_nonzero q l P c weight h a f p s v w hn⟩

include hyper weight in
theorem obstructed (h a : ℕ) (ho : Y + 3*(h : ℤ) - 3*a ≠ 0 ∨ c ≠ 0) :
    SelectionCriteria.Forbidden (Space q l P h a) := by
  intro f
  by_contra hf
  have hh := necessary q l P Y c hyper weight h a ⟨f,hf⟩
  rcases ho with hy | hc
  · exact hy hh.1
  · exact hc hh.2


include hyper in
theorem hypercharge_divisible (h a : ℕ) (hf : SelectionCriteria.Allowed (Space q l P h a)) :
    (3 : ℤ) ∣ Y := by
  obtain ⟨f,hf⟩ := hf
  obtain ⟨p,s,v,w,hn⟩ := exists_value q l P h a f hf
  have hh := hypercharge_of_nonzero q l P Y hyper h a f p s v w hn
  refine ⟨(a : ℤ)-h, ?_⟩
  linear_combination hh

include hyper in
theorem indivisible_forbidden (hy : ¬ (3 : ℤ) ∣ Y) (h a : ℕ) :
    SelectionCriteria.Forbidden (Space q l P h a) := by
  intro f
  by_contra hf
  exact hy (hypercharge_divisible q l P Y hyper h a ⟨f,hf⟩)

/-- Odd degree is a genuine whole-space obstruction, not a missing seed. -/
theorem odd_forbidden (h a : ℕ) (hn : n % 2 ≠ 0) :
    SelectionCriteria.Forbidden (Space q l P h a) := by
  intro f
  apply Subtype.ext
  exact AdmittedCyclicSMProhibition.odd_coefficients_zero (flavor q l) scalar n (h+a) hn f.val


/-- The existing finite fermion universe excludes all larger degrees. -/
theorem above_bound_forbidden (h a : ℕ) (hn : 180 < n) :
    SelectionCriteria.Forbidden (Space q l P h a) := by
  intro f
  apply Subtype.ext
  exact ThreeGenerationFermionBound.coefficients_zero (flavor q l) scalar n (h+a) hn f.val

section NeutralHypercharge
variable (hyper0 : ∀ p, P p → ∑ i, hypercharge (p i) = 0)

def rawDress (r : ℕ) (f : SeedSpace q l P) :
    BnvMixedInput.Coefficient (flavor q l) scalar n (r+r) :=
  MixedInvariantDressing.product f.val (DuqlHiggsContent.balancedScalar r)

include hyper0 in
theorem rawDress_mem (r : ℕ) (f : SeedSpace q l P) :
    rawDress q l P r f ∈ Space q l P r r := by
  intro p s hs v w
  change BnvMixedInput.value (flavor q l) scalar (rawDress q l P r f) p s v w = 0
  by_contra hn
  have hp : P p := by
    by_contra hp
    have hz := congrArg (fun t => t v) (f.property p hp)
    have he : BnvMixedInput.value (flavor q l) scalar (rawDress q l P r f) p s v w =
      FiniteSpeciesExterior.restrict (DeltaLOneSignedFields.field (flavor q l)) f.val p v *
      DuqlHiggsContent.balancedScalar (k := k) r (SymmetricPower.tprod ℂ (fun j => Pi.single (s j) (w j))) :=
        MixedInvariantDressing.product_apply _ _ _ _
    rw [he, hz] at hn
    exact hn (by simp)
  have hy := BnvMixedInput.hypercharge_of_nonzero (flavor q l) scalar (rawDress q l P r f) p s v w hn
  rw [hyper0 p hp, scalar_hypercharge, zero_add] at hy
  have ht := scalarCount_total s
  exact hs ⟨hp, by omega, by omega⟩

include hyper0 in
def dress (r : ℕ) (f : SeedSpace q l P) : Space q l P r r :=
  ⟨rawDress q l P r f, rawDress_mem q l P hyper0 r f⟩

include hyper0 in
theorem dress_nonzero (r : ℕ) (f : SeedSpace q l P) (hf : f ≠ 0) :
    dress q l P hyper0 r f ≠ 0 := by
  intro hz
  have hh : f.val ≠ 0 := fun h => hf (Subtype.ext h)
  exact MixedInvariantDressing.product_nonzero _ _ hh (DuqlHiggsContent.balancedScalar_nonzero r)
    (congrArg Subtype.val hz)

include hyper0 weight in
theorem allowed_iff (seed : c=0 → SelectionCriteria.Allowed (SeedSpace q l P)) (h a : ℕ) :
    SelectionCriteria.Allowed (Space q l P h a) ↔ h=a ∧ c=0 := by
  constructor
  · intro hh
    have hn := necessary q l P 0 c hyper0 weight h a hh
    exact ⟨by omega, hn.2⟩
  · rintro ⟨rfl,hc⟩
    obtain ⟨f,hf⟩ := seed hc
    exact ⟨dress q l P hyper0 h f, dress_nonzero q l P hyper0 h f hf⟩

include hyper0 weight in
theorem forbidden_iff (seed : c=0 → SelectionCriteria.Allowed (SeedSpace q l P)) (h a : ℕ) :
    SelectionCriteria.Forbidden (Space q l P h a) ↔ h≠a ∨ c≠0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, allowed_iff q l P c weight hyper0 seed]
  exact not_and_or

include hyper0 weight in
theorem all_forbidden_iff (seed : c=0 → SelectionCriteria.Allowed (SeedSpace q l P)) :
    (∀ h a, SelectionCriteria.Forbidden (Space q l P h a)) ↔ c≠0 := by
  constructor
  · intro hh
    exact ((forbidden_iff q l P c weight hyper0 seed 0 0).mp (hh 0 0)).resolve_left (by simp)
  · intro hc h a
    exact (forbidden_iff q l P c weight hyper0 seed h a).mpr (Or.inr hc)

end NeutralHypercharge

/-- The four previously certified contents discharge every adapter premise. -/
def family (i : Fin 4) (p : Fin 4 → Species) : Prop :=
  counts p = DeltaLOneFourFamilyDecomposition.familyCounts i

theorem family_stable (i : Fin 4) (p : Fin 4 → Species) (e : Equiv.Perm (Fin 4)) :
    family i (p ∘ e) ↔ family i p := by
  simp only [family, DeltaLOneFourFamilyDecomposition.counts_perm]

theorem family_hyper (i : Fin 4) (p : Fin 4 → Species) (hp : family i p) :
    ∑ j, hypercharge (p j) = 0 := by
  rw [← hypercharge_counts, hp]
  exact FourFamilyHiggsContent.family_hypercharge i

omit [NeZero k] in
theorem family_weight (i : Fin 4) (p : Fin 4 → Species) (hp : family i p) :
    ∑ j, charge q l (p j) = 3*q+l := FourFamilyHiggsContent.family_charge q l i p hp

theorem family_seed (i : Fin 4) (hc : 3*q+l=0) :
    SelectionCriteria.Allowed (SeedSpace q l (family i)) := by
  obtain ⟨coord⟩ := (FourFamilyHiggsContent.indices_nonempty_iff q l i).mpr hc
  let c : FourFamilyHiggsContent.Indices q l i → ℂ := fun _ => 1
  have hn : c ≠ 0 := by intro h; have he := congrFun h coord; norm_num [c] at he
  let b := FourFamilyHiggsContent.base q l i c
  have hb : b ≠ 0 := by
    intro h
    apply hn
    apply FourFamilyHiggsContent.base_injective q l i
    have hz : FourFamilyHiggsContent.base q l i 0 = 0 :=
      (FourFamilyHiggsContent.baseEquiv q l i).symm.map_zero
    exact h.trans hz.symm
  refine ⟨⟨b.val,b.property⟩,?_⟩
  intro hz
  exact hb (Subtype.ext (congrArg Subtype.val hz))

theorem family_control (i : Fin 4) (h a : ℕ) :
    Space q l (family i) h a = FourFamilyHiggsContent.CyclicSpace q l i h a := rfl

/-- Four-family iff recovered through the generic content adapter. -/
theorem family_allowed_iff (i : Fin 4) (h a : ℕ) :
    SelectionCriteria.Allowed (FourFamilyHiggsContent.CyclicSpace q l i h a) ↔
      h=a ∧ 3*q+l=0 := by
  exact allowed_iff q l (family i) (3*q+l) (family_weight q l i) (family_hyper i)
    (family_seed q l i) h a

/-- A concrete nonzero-hypercharge content cannot use balanced dressing. -/
def leptonPair (p : Fin 2 → Species) : Prop := ∀ j, p j = 3

theorem leptonPair_hyper (p : Fin 2 → Species) (hp : leptonPair p) :
    ∑ j, hypercharge (p j) = -6 := by
  have he : p = fun _ => 3 := funext hp
  rw [he]
  norm_num [hypercharge]

omit [NeZero k] in
theorem leptonPair_weight (p : Fin 2 → Species) (hp : leptonPair p) :
    ∑ j, charge q l (p j) = 2*l := by
  have he : p = fun _ => 3 := funext hp
  rw [he]
  simp [charge, DuqlHiggsContent.signedCharge]

theorem leptonPair_necessary (h a : ℕ)
    (hf : SelectionCriteria.Allowed (Space q l leptonPair h a)) : h=a+2 ∧ 2*l=0 := by
  have hh := necessary q l leptonPair (-6) (2*l) leptonPair_hyper
    (leptonPair_weight q l) h a hf
  exact ⟨by omega,hh.2⟩

/-- Balance is not a universal condition: this content requires two extra Higgs fields. -/
theorem leptonPair_balanced_forbidden (r : ℕ) :
    SelectionCriteria.Forbidden (Space q l leptonPair r r) := by
  apply obstructed q l leptonPair (-6) (2*l) leptonPair_hyper (leptonPair_weight q l)
  left
  omega

end
end Physics.ContentHiggsSupport
