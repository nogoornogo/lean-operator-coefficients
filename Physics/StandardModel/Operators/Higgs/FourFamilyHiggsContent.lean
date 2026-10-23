import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DuqlHiggsContent

/-! Full fixed four-family content, defined by species support on the actual mixed
exterior/symmetric coefficient space, independently of any seed list. -/
namespace Physics.FourFamilyHiggsContent
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
open DuqlHiggsContent (scalarCount scalarCount_perm scalar_hypercharge scalarCount_total)
open scoped BigOperators TensorProduct

def support (i : Fin 4) (h a : ℕ) (p : Fin 4 → Species)
    (s : Fin (h+a) → BnvMixedInput.ScalarSpecies) : Prop :=
  counts p = DeltaLOneFourFamilyDecomposition.familyCounts i ∧ scalarCount s 0 = h ∧ scalarCount s 1 = a

instance (i : Fin 4) (h a : ℕ) (p : Fin 4 → Species)
    (s : Fin (h+a) → BnvMixedInput.ScalarSpecies) : Decidable (support i h a p s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem support_stable (i : Fin 4) (h a : ℕ) (p : Fin 4 → Species)
    (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (e : Equiv.Perm (Fin 4)) (f : Equiv.Perm (Fin (h+a))) :
    support i h a (p ∘ e) (s ∘ f) ↔ support i h a p s := by
  simp only [support, DeltaLOneFourFamilyDecomposition.counts_perm, scalarCount_perm]

theorem family_hypercharge (i : Fin 4) :
    DeltaLOneSpeciesSupport.sixHypercharge (DeltaLOneFourFamilyDecomposition.familyCounts i) = 0 := by
  fin_cases i <;> rfl

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ R (F u))
  (scalarFlavor : ∀ u, Representation ℂ R (S u))

/-- The entire actual fixed-content space, not a range of dressing seeds. -/
abbrev Space (i : Fin 4) (h a : ℕ) := MixedSpeciesProjection.supportSpace (support i h a)
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)

def project (i : Fin 4) (h a : ℕ) : BnvMixedInput.Coefficient flavor scalarFlavor 4 (h+a) →ₗ[ℂ]
    Space flavor scalarFlavor i h a :=
  (MixedSpeciesProjection.projectLinear (support i h a) (support_stable i h a)
    (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)).codRestrict _
    (MixedSpeciesProjection.project_mem (support i h a) (support_stable i h a) _ _)

theorem project_value (i : Fin 4) (h a : ℕ)
    (f : BnvMixedInput.Coefficient flavor scalarFlavor 4 (h+a))
    (p : Fin 4 → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j)) :
    BnvMixedInput.value flavor scalarFlavor (project flavor scalarFlavor i h a f).val p s v w =
      if support i h a p s then BnvMixedInput.value flavor scalarFlavor f p s v w else 0 := by
  exact MixedSpeciesProjection.project_pure (support i h a) (support_stable i h a) _ _ _ _ _

theorem project_eq_self (i : Fin 4) (h a : ℕ) (f : Space flavor scalarFlavor i h a) :
    (project flavor scalarFlavor i h a f.val).val = f.val :=
  MixedSpeciesProjection.project_eq_self (support i h a) (support_stable i h a) _ _ f

theorem balance_of_nonzero (i : Fin 4) (h a : ℕ) (f : Space flavor scalarFlavor i h a)
    (p : Fin 4 → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j))
    (hn : BnvMixedInput.value flavor scalarFlavor f.val p s v w ≠ 0) : h = a := by
  have hs : support i h a p s := by
    by_contra hs
    exact hn (f.property p s hs v w)
  have hy := BnvMixedInput.hypercharge_of_nonzero flavor scalarFlavor f.val p s v w hn
  rw [← hypercharge_counts, hs.1, scalar_hypercharge, hs.2.1, hs.2.2] at hy
  rw [family_hypercharge, zero_add] at hy
  omega

theorem unequal_zero (i : Fin 4) (h a : ℕ) (ha : h ≠ a) (f : Space flavor scalarFlavor i h a) : f = 0 := by
  apply Subtype.ext
  apply BnvMixedInput.value_ext flavor scalarFlavor
  intro p s v w
  change BnvMixedInput.value flavor scalarFlavor f.val p s v w = 0
  by_contra hn
  exact ha (balance_of_nonzero flavor scalarFlavor i h a f p s v w hn)

/-- Union of the four actual species contents, independent of contraction seeds. -/
abbrev CombinedSpace (h a : ℕ) := MixedSpeciesProjection.supportSpace
  (fun p s => ∃ i : Fin 4, support i h a p s)
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)

theorem combined_mem (i : Fin 4) (h a : ℕ) (f : Space flavor scalarFlavor i h a) :
    f.val ∈ CombinedSpace flavor scalarFlavor h a := by
  intro p s hs v w
  exact f.property p s (fun hi => hs ⟨i,hi⟩) v w

/-- No information is lost when testing prohibition separately on the four contents. -/
theorem combined_forbidden_iff (h a : ℕ) :
    SelectionCriteria.Forbidden (CombinedSpace flavor scalarFlavor h a) ↔
      ∀ i : Fin 4, SelectionCriteria.Forbidden (Space flavor scalarFlavor i h a) := by
  constructor
  · intro hh i f
    apply Subtype.ext
    let u : CombinedSpace flavor scalarFlavor h a := ⟨f.val, combined_mem flavor scalarFlavor i h a f⟩
    exact congrArg (fun g : CombinedSpace flavor scalarFlavor h a => g.val) (hh u)
  · intro hh f
    apply Subtype.ext
    apply BnvMixedInput.value_ext flavor scalarFlavor
    intro p s v w
    change BnvMixedInput.value flavor scalarFlavor f.val p s v w = 0
    by_cases hs : ∃ i : Fin 4, support i h a p s
    · obtain ⟨i,hi⟩ := hs
      have he := congrArg (fun g : Space flavor scalarFlavor i h a =>
        BnvMixedInput.value flavor scalarFlavor g.val p s v w)
        (hh i (project flavor scalarFlavor i h a f.val))
      have hp := project_value flavor scalarFlavor i h a f.val p s v w
      rw [ite_eq_left hi] at hp
      exact hp.symm.trans he
    · exact f.property p s hs v w

end
noncomputable section Cyclic
open Math Representation DeltaLOneSignedInput
open DuqlHiggsContent (scalarCount scalarCount_perm scalar_hypercharge scalarCount_total)
variable {k : ℕ} [NeZero k] (q l : ZMod k)

abbrev fermionFlavor := DressedDuqlFamily.flavor q l
abbrev scalarFlavor := NeutralHiggsPowers.flavor (H := CyclicCharge.Group k)
abbrev CyclicSpace (i : Fin 4) (h a : ℕ) := Space (fermionFlavor q l) (scalarFlavor (k := k)) i h a

abbrev signedCharge := DuqlHiggsContent.signedCharge q l

omit [NeZero k] in
theorem family_charge (i : Fin 4) (p : Fin 4 → Species)
    (hp : counts p = DeltaLOneFourFamilyDecomposition.familyCounts i) :
    ∑ j, signedCharge q l (p j) = 3*q+l := by
  rw [sum_weights]
  have hc := DeltaLOneFourFamilyDecomposition.multiplicities_eq_of_counts p
    (DeltaLOneFourFamilyDecomposition.pattern i)
    (hp.trans (DeltaLOneFourFamilyDecomposition.counts_pattern i).symm)
  simp_rw [hc]
  rw [← sum_weights]
  fin_cases i <;> simp [signedCharge, DuqlHiggsContent.signedCharge, DeltaLOneFourFamilyDecomposition.pattern,
    Fin.sum_univ_succ] <;> ring

theorem charge_of_nonzero (i : Fin 4) (h a : ℕ) (f : CyclicSpace q l i h a)
    (p : Fin 4 → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) (s j))
    (hn : BnvMixedInput.value (fermionFlavor q l) scalarFlavor f.val p s v w ≠ 0) :
    3*q+l = 0 := by
  have hs : support i h a p s := by
    by_contra hs
    exact hn (f.property p s hs v w)
  apply (CyclicCharge.neutral_iff (3*q+l)).mp
  intro g
  have he := MixedWeightSupport.scalar_constraint
    (FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field (fermionFlavor q l)))
    (FiniteSpeciesExterior.representation (BnvMixedInput.scalarField (scalarFlavor (k := k)))) f.val (1,g)
    (fun i => Pi.single (p i) (v i)) (fun j => Pi.single (s j) (w j))
    (fun i => MixedChargeSelection.cyclicCharacter g (signedCharge q l (p i)))
    (fun _ => (1 : ℂ))
    (by
      intro i
      rw [FiniteSpeciesExterior.action_single, DuqlHiggsContent.field_scalar]
      exact Pi.single_smul _ _ _)
    (by
      intro j
      rw [FiniteSpeciesExterior.action_single, DuqlHiggsContent.boson_scalar]
      simp)
  simp only [Finset.prod_const_one, mul_one] at he
  have hh := MixedChargeSelection.total_eq_character (MixedChargeSelection.cyclicCharacter g)
    (signedCharge q l) (fun _ : BnvMixedInput.ScalarSpecies => (0 : ZMod k)) p s
  simp only [MixedScalarSelection.total, AddChar.map_zero_eq_one, Finset.prod_const_one, mul_one,
    MixedChargeSelection.charge, Finset.sum_const_zero, add_zero] at hh
  rw [hh, family_charge q l i p hs.1] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hn)

theorem nonneutral_zero (i : Fin 4) (h a : ℕ) (hz : 3*q+l ≠ 0) (f : CyclicSpace q l i h a) : f = 0 := by
  apply Subtype.ext
  apply BnvMixedInput.value_ext (fermionFlavor q l) scalarFlavor
  intro p s v w
  change BnvMixedInput.value (fermionFlavor q l) scalarFlavor f.val p s v w = 0
  by_contra hn
  exact hz (charge_of_nonzero q l i h a f p s v w hn)

abbrev Indices (i : Fin 4) := match i with
  | 0 => FlavoredCyclicSelection.DuqlIndex (fun _ : Fin 5 => Fin 3) (InverseCyclicSMCharges.universal q l)
  | 1 => FlavoredCyclicSelection.QqueIndex (fun _ : Fin 5 => Fin 3) (InverseCyclicSMCharges.universal q l)
  | 2 => FlavoredCyclicSelection.QqqlIndex (fun _ : Fin 5 => Fin 3) (InverseCyclicSMCharges.universal q l)
  | 3 => FlavoredCyclicSelection.DuueIndex (fun _ : Fin 5 => Fin 3) (InverseCyclicSMCharges.universal q l)

omit [NeZero k] in
theorem indices_nonempty_iff (i : Fin 4) : Nonempty (Indices q l i) ↔ 3*q+l=0 := by
  fin_cases i
  · exact DressedDuqlFamily.indices_nonempty_iff q l
  · constructor
    · rintro ⟨p⟩
      exact (InverseCyclicSMCharges.universal_qque_charge q l p.val).symm.trans p.property
    · intro hz
      refine ⟨⟨(TauCeti.Sym.ofFn (fun _ : Fin 2 => (0 : Fin 3)), (0,0)),?_⟩⟩
      exact (InverseCyclicSMCharges.universal_qque_charge q l _).trans hz
  · constructor
    · rintro ⟨p⟩
      exact (InverseCyclicSMCharges.universal_qqql_charge q l p.val).symm.trans p.property
    · intro hz
      refine ⟨⟨(0, Sum.inl ⟨(0,0,0), le_rfl, le_rfl⟩),?_⟩⟩
      exact (InverseCyclicSMCharges.universal_qqql_charge q l _).trans hz
  · constructor
    · rintro ⟨p⟩
      have hp := p.property
      simpa [FlavoredCyclicCoordinates.fourCharge, InverseCyclicSMCharges.universal,
        InverseCyclicSMCharges.physical, show (3 : ZMod k)*q=q+q+q by ring, add_assoc] using hp
    · intro hz
      refine ⟨⟨((0,0),(0,0)),?_⟩⟩
      simp [FlavoredCyclicCoordinates.fourCharge, InverseCyclicSMCharges.universal,
        InverseCyclicSMCharges.physical]
      linear_combination hz

/-- Transport through each actual statistics-aware zero-Higgs dictionary. -/
def baseEquiv (i : Fin 4) : DeltaLOneFourFamilyDecomposition.FamilySector (fermionFlavor q l) i ≃ₗ[ℂ]
    (Indices q l i → ℂ) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => nomatch j)))) i
  · exact DuqlHiggsContent.baseEquiv q l
  · exact (DeltaLOneFamilyCompleteness.qqueEquiv (fermionFlavor q l)).trans
      (FlavoredCyclicSelection.qqueResidualEquiv _ (InverseCyclicSMCharges.universal q l))
  · exact (DeltaLOneFamilyCompleteness.qqqlEquiv (fermionFlavor q l)).trans
      (FlavoredCyclicSelection.qqqlResidualEquiv _ (InverseCyclicSMCharges.universal q l))
  · exact (DeltaLOneFamilyCompleteness.duueEquiv (fermionFlavor q l)).trans
      (FlavoredCyclicSelection.duueResidualEquiv _ (InverseCyclicSMCharges.universal q l))

def base (i : Fin 4) (c : Indices q l i → ℂ) := (baseEquiv q l i).symm c

theorem base_injective (i : Fin 4) : Function.Injective (base q l i) := (baseEquiv q l i).symm.injective


def rawDress (i : Fin 4) (r : ℕ) (c : Indices q l i → ℂ) :
    BnvMixedInput.Coefficient (fermionFlavor q l) scalarFlavor 4 (r+r) :=
  MixedInvariantDressing.product (base q l i c).val (DuqlHiggsContent.balancedScalar r)

theorem rawDress_value (i : Fin 4) (r : ℕ) (c : Indices q l i → ℂ)
    (p : Fin 4 → Species) (s : Fin (r+r) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) (s j)) :
    BnvMixedInput.value (fermionFlavor q l) scalarFlavor (rawDress q l i r c) p s v w =
      FiniteSpeciesExterior.restrict (DeltaLOneSignedFields.field (fermionFlavor q l))
        (base q l i c).val p v *
      DuqlHiggsContent.balancedScalar (k := k) r (SymmetricPower.tprod ℂ (fun j => Pi.single (s j) (w j))) := by
  exact MixedInvariantDressing.product_apply _ _ _ _

theorem rawDress_mem (i : Fin 4) (r : ℕ) (c : Indices q l i → ℂ) :
    rawDress q l i r c ∈ Space (fermionFlavor q l) scalarFlavor i r r := by
  intro p s hs v w
  change BnvMixedInput.value (fermionFlavor q l) scalarFlavor (rawDress q l i r c) p s v w = 0
  by_contra hn
  have hp : counts p = DeltaLOneFourFamilyDecomposition.familyCounts i := by
    by_contra hp
    have hz := (base q l i c).property p hp
    rw [rawDress_value, hz] at hn
    exact hn (by simp)
  have hy := BnvMixedInput.hypercharge_of_nonzero (fermionFlavor q l) scalarFlavor
    (rawDress q l i r c) p s v w hn
  rw [← hypercharge_counts, hp, scalar_hypercharge] at hy
  rw [family_hypercharge, zero_add] at hy
  have ht := scalarCount_total s
  exact hs ⟨hp, by omega, by omega⟩

def dressed (i : Fin 4) (r : ℕ) (c : Indices q l i → ℂ) : CyclicSpace q l i r r :=
  ⟨rawDress q l i r c, rawDress_mem q l i r c⟩

theorem dressed_nonzero (i : Fin 4) (r : ℕ) (c : Indices q l i → ℂ) (hc : c ≠ 0) :
    dressed q l i r c ≠ 0 := by
  intro hz
  have hb : (base q l i c).val ≠ 0 := by
    intro hh
    apply hc
    apply base_injective q l i
    apply Subtype.ext
    have hb0 : base q l i 0 = 0 := by
      exact (baseEquiv q l i).symm.map_zero
    rw [hb0]
    exact hh
  exact MixedInvariantDressing.product_nonzero _ _ hb (DuqlHiggsContent.balancedScalar_nonzero r)
    (congrArg Subtype.val hz)

/-- Support of the whole actual fixed-content space, without a spanning premise. -/
theorem allowed_iff (i : Fin 4) (h a : ℕ) : SelectionCriteria.Allowed (CyclicSpace q l i h a) ↔
    h = a ∧ 3*q+l = 0 := by
  constructor
  · rintro ⟨f,hf⟩
    have hex : ∃ p s v w, BnvMixedInput.value (fermionFlavor q l) scalarFlavor f.val p s v w ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hf
      apply Subtype.ext
      apply BnvMixedInput.value_ext (fermionFlavor q l) scalarFlavor
      intro p s v w
      change BnvMixedInput.value (fermionFlavor q l) scalarFlavor f.val p s v w = 0
      exact hn p s v w
    obtain ⟨p,s,v,w,hn⟩ := hex
    exact ⟨balance_of_nonzero _ _ i h a f p s v w hn,
      charge_of_nonzero q l i h a f p s v w hn⟩
  · rintro ⟨rfl,hz⟩
    obtain ⟨coord⟩ := (indices_nonempty_iff q l i).mpr hz
    let c : Indices q l i → ℂ := fun _ => 1
    have hc : c ≠ 0 := by intro hh; have hi := congrFun hh coord; norm_num [c] at hi
    exact ⟨dressed q l i h c, dressed_nonzero q l i h c hc⟩

theorem forbidden_iff (i : Fin 4) (h a : ℕ) : SelectionCriteria.Forbidden (CyclicSpace q l i h a) ↔
    h ≠ a ∨ 3*q+l ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, allowed_iff]
  exact not_and_or


/-- Exact all-Higgs prohibition for this content only. -/
theorem all_forbidden_iff (i : Fin 4) : (∀ h a, SelectionCriteria.Forbidden (CyclicSpace q l i h a)) ↔
    3*q+l ≠ 0 := by
  constructor
  · intro hh
    have h0 := (forbidden_iff q l i 0 0).mp (hh 0 0)
    exact h0.resolve_left (by simp)
  · intro hz h a
    exact (forbidden_iff q l i h a).mpr (Or.inr hz)


/-- DUQL is the zero-index instance of the shared whole-content definition. -/
theorem duql_control (h a : ℕ) : CyclicSpace q l 0 h a = DuqlHiggsContent.CyclicSpace q l h a := rfl

/-- Prohibition of the union of all four selected contents at each scalar count. -/
theorem combined_cyclic_forbidden_iff (h a : ℕ) :
    SelectionCriteria.Forbidden (CombinedSpace (fermionFlavor q l) scalarFlavor h a) ↔
      h ≠ a ∨ 3*q+l ≠ 0 := by
  rw [combined_forbidden_iff]
  constructor
  · intro hh; exact (forbidden_iff q l 0 h a).mp (hh 0)
  · intro hh i; exact (forbidden_iff q l i h a).mpr hh

theorem combined_cyclic_allowed_iff (h a : ℕ) :
    SelectionCriteria.Allowed (CombinedSpace (fermionFlavor q l) scalarFlavor h a) ↔
      h = a ∧ 3*q+l = 0 := by
  rw [← not_iff_not, ← SelectionCriteria.forbidden_iff_not_allowed, combined_cyclic_forbidden_iff]
  exact not_and_or.symm

theorem all_four_forbidden_iff :
    (∀ h a, SelectionCriteria.Forbidden (CombinedSpace (fermionFlavor q l) scalarFlavor h a)) ↔
      3*q+l ≠ 0 := by
  constructor
  · intro hh
    exact ((combined_cyclic_forbidden_iff q l 0 0).mp (hh 0 0)).resolve_left (by simp)
  · intro hh h a
    exact (combined_cyclic_forbidden_iff q l h a).mpr (Or.inr hh)

end Cyclic
end Physics.FourFamilyHiggsContent
