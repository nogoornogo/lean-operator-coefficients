import Physics.StandardModel.Operators.BaryonOne.OtherFamilies.DressedDuqlFamily

/-! Full fixed DUQL content, defined by species support on the actual mixed
exterior/symmetric coefficient space, independently of any seed list. -/
namespace Physics.DuqlHiggsContent
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
open scoped BigOperators TensorProduct

variable {m : ℕ}
def scalarCount (s : Fin m → BnvMixedInput.ScalarSpecies)
    (u : BnvMixedInput.ScalarSpecies) : ℕ :=
  (Finset.univ.filter (fun i => s i = u)).card

theorem scalarCount_perm (s : Fin m → BnvMixedInput.ScalarSpecies)
    (p : Equiv.Perm (Fin m)) (u : BnvMixedInput.ScalarSpecies) :
    scalarCount (s ∘ p) u = scalarCount s u := by
  unfold scalarCount
  apply Finset.card_equiv p
  intro i
  simp [Function.comp_apply]

theorem scalar_sum_weights (s : Fin m → BnvMixedInput.ScalarSpecies)
    {A : Type*} [AddCommMonoid A] (w : BnvMixedInput.ScalarSpecies → A) :
    ∑ i, w (s i) = ∑ u, scalarCount s u • w u := by
  rw [← Finset.sum_fiberwise_of_maps_to' (fun i (_ : i ∈ Finset.univ) =>
    Finset.mem_univ (s i)) w]
  simp [scalarCount, Finset.sum_const]

theorem scalarCount_total (s : Fin m → BnvMixedInput.ScalarSpecies) :
    scalarCount s 0 + scalarCount s 1 = m := by
  have h := scalar_sum_weights s (fun _ => (1 : ℕ))
  simpa [Fin.sum_univ_succ] using h.symm

theorem scalar_hypercharge (s : Fin m → BnvMixedInput.ScalarSpecies) :
    ∑ i, BnvMixedInput.scalarHypercharge (s i) =
      3 * (scalarCount s 0 : ℤ) - 3 * scalarCount s 1 := by
  rw [scalar_sum_weights]
  simp [BnvMixedInput.scalarHypercharge, Fin.sum_univ_succ]
  ring

def support (h a : ℕ) (p : Fin 4 → Species)
    (s : Fin (h+a) → BnvMixedInput.ScalarSpecies) : Prop :=
  counts p = DeltaLOneSpeciesSupport.duql ∧ scalarCount s 0 = h ∧ scalarCount s 1 = a

instance (h a : ℕ) (p : Fin 4 → Species)
    (s : Fin (h+a) → BnvMixedInput.ScalarSpecies) : Decidable (support h a p s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem support_stable (h a : ℕ) (p : Fin 4 → Species)
    (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (e : Equiv.Perm (Fin 4)) (f : Equiv.Perm (Fin (h+a))) :
    support h a (p ∘ e) (s ∘ f) ↔ support h a p s := by
  simp only [support, DeltaLOneFourFamilyDecomposition.counts_perm, scalarCount_perm]

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ R (F u))
  (scalarFlavor : ∀ u, Representation ℂ R (S u))

/-- The entire actual fixed-content space, not a range of dressing seeds. -/
abbrev Space (h a : ℕ) := MixedSpeciesProjection.supportSpace (support h a)
  (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)

def project (h a : ℕ) : BnvMixedInput.Coefficient flavor scalarFlavor 4 (h+a) →ₗ[ℂ]
    Space flavor scalarFlavor h a :=
  (MixedSpeciesProjection.projectLinear (support h a) (support_stable h a)
    (DeltaLOneSignedFields.field flavor) (BnvMixedInput.scalarField scalarFlavor)).codRestrict _
    (MixedSpeciesProjection.project_mem (support h a) (support_stable h a) _ _)

theorem project_value (h a : ℕ)
    (f : BnvMixedInput.Coefficient flavor scalarFlavor 4 (h+a))
    (p : Fin 4 → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j)) :
    BnvMixedInput.value flavor scalarFlavor (project flavor scalarFlavor h a f).val p s v w =
      if support h a p s then BnvMixedInput.value flavor scalarFlavor f p s v w else 0 := by
  exact MixedSpeciesProjection.project_pure (support h a) (support_stable h a) _ _ _ _ _

theorem project_eq_self (h a : ℕ) (f : Space flavor scalarFlavor h a) :
    (project flavor scalarFlavor h a f.val).val = f.val :=
  MixedSpeciesProjection.project_eq_self (support h a) (support_stable h a) _ _ f

theorem balance_of_nonzero (h a : ℕ) (f : Space flavor scalarFlavor h a)
    (p : Fin 4 → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j))
    (hn : BnvMixedInput.value flavor scalarFlavor f.val p s v w ≠ 0) : h = a := by
  have hs : support h a p s := by
    by_contra hs
    exact hn (f.property p s hs v w)
  have hy := BnvMixedInput.hypercharge_of_nonzero flavor scalarFlavor f.val p s v w hn
  rw [← hypercharge_counts, hs.1, scalar_hypercharge, hs.2.1, hs.2.2] at hy
  norm_num [DeltaLOneSpeciesSupport.sixHypercharge, DeltaLOneSpeciesSupport.duql] at hy
  omega

theorem unequal_zero (h a : ℕ) (ha : h ≠ a) (f : Space flavor scalarFlavor h a) : f = 0 := by
  apply Subtype.ext
  apply BnvMixedInput.value_ext flavor scalarFlavor
  intro p s v w
  change BnvMixedInput.value flavor scalarFlavor f.val p s v w = 0
  by_contra hn
  exact ha (balance_of_nonzero flavor scalarFlavor h a f p s v w hn)
end
noncomputable section Cyclic
open Math Representation DeltaLOneSignedInput
variable {k : ℕ} [NeZero k] (q l : ZMod k)

abbrev fermionFlavor := DressedDuqlFamily.flavor q l
abbrev scalarFlavor := NeutralHiggsPowers.flavor (H := CyclicCharge.Group k)
abbrev CyclicSpace (h a : ℕ) := Space (fermionFlavor q l) (scalarFlavor (k := k)) h a

def signedCharge : Species → ZMod k := ![q,q,q,l,l,-q,-q,-q,-l,-l]

omit [NeZero k] in
theorem duql_charge (p : Fin 4 → Species) (hp : counts p = DeltaLOneSpeciesSupport.duql) :
    ∑ i, signedCharge q l (p i) = 3*q+l := by
  rw [sum_weights]
  have hc := DeltaLOneFourFamilyDecomposition.multiplicities_eq_of_counts p
    (DeltaLOneFourFamilyDecomposition.pattern 0)
    (hp.trans (DeltaLOneFourFamilyDecomposition.counts_pattern 0).symm)
  simp_rw [hc]
  rw [← sum_weights]
  simp [signedCharge, DeltaLOneFourFamilyDecomposition.pattern, Fin.sum_univ_succ]
  ring

theorem flavor_scalar (g : CyclicCharge.Group k) (u : Species)
    (v : FlavoredCyclicSelection.signedIndex (fun _ : Fin 5 => Fin 3) u → ℂ) :
    fermionFlavor q l u g v = MixedChargeSelection.cyclicCharacter g (signedCharge q l u) • v := by
  funext i
  fin_cases u <;> rfl

theorem field_scalar (g : CyclicCharge.Group k) (u : Species)
    (x : DeltaLOneSignedFields.Field (F := fun u =>
      FlavoredCyclicSelection.signedIndex (fun _ : Fin 5 => Fin 3) u → ℂ) u) :
    DeltaLOneSignedFields.field (fermionFlavor q l) u (1,g) x =
      MixedChargeSelection.cyclicCharacter g (signedCharge q l u) • x := by
  have he : DeltaLOneSignedFields.field (fermionFlavor q l) u (1,g) =
      MixedChargeSelection.cyclicCharacter g (signedCharge q l u) • LinearMap.id := by
    apply TensorProduct.ext'
    intro v w
    simp [DeltaLOneSignedFields.field, ExternalInvariantTensor.external,
      Representation.tprod_apply, flavor_scalar, TensorProduct.tmul_smul]
  exact LinearMap.congr_fun he x

omit [NeZero k] in
theorem boson_scalar (g : CyclicCharge.Group k) (u : BnvMixedInput.ScalarSpecies)
    (x : BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) u) :
    BnvMixedInput.scalarField (scalarFlavor (k := k)) u (1,g) x = x := by
  have he : BnvMixedInput.scalarField (scalarFlavor (k := k)) u (1,g) = LinearMap.id := by
    apply TensorProduct.ext'
    intro v w
    simp [BnvMixedInput.scalarField, ExternalInvariantTensor.external,
      Representation.tprod_apply, scalarFlavor, NeutralHiggsPowers.flavor]
  exact LinearMap.congr_fun he x

theorem charge_of_nonzero (h a : ℕ) (f : CyclicSpace q l h a)
    (p : Fin 4 → Species) (s : Fin (h+a) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) (s j))
    (hn : BnvMixedInput.value (fermionFlavor q l) scalarFlavor f.val p s v w ≠ 0) :
    3*q+l = 0 := by
  have hs : support h a p s := by
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
      rw [FiniteSpeciesExterior.action_single, field_scalar]
      exact Pi.single_smul _ _ _)
    (by
      intro j
      rw [FiniteSpeciesExterior.action_single, boson_scalar]
      simp)
  simp only [Finset.prod_const_one, mul_one] at he
  have hh := MixedChargeSelection.total_eq_character (MixedChargeSelection.cyclicCharacter g)
    (signedCharge q l) (fun _ : BnvMixedInput.ScalarSpecies => (0 : ZMod k)) p s
  simp only [MixedScalarSelection.total, AddChar.map_zero_eq_one, Finset.prod_const_one, mul_one,
    MixedChargeSelection.charge, Finset.sum_const_zero, add_zero] at hh
  rw [hh, duql_charge q l p hs.1] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hn)

theorem nonneutral_zero (h a : ℕ) (hz : 3*q+l ≠ 0) (f : CyclicSpace q l h a) : f = 0 := by
  apply Subtype.ext
  apply BnvMixedInput.value_ext (fermionFlavor q l) scalarFlavor
  intro p s v w
  change BnvMixedInput.value (fermionFlavor q l) scalarFlavor f.val p s v w = 0
  by_contra hn
  exact hz (charge_of_nonzero q l h a f p s v w hn)

/-- Full zero-Higgs DUQL factor from the previously proved actual dictionary. -/
def baseEquiv : DeltaLOneFourFamilyDecomposition.FamilySector (fermionFlavor q l) 0 ≃ₗ[ℂ]
    (DressedDuqlFamily.Indices q l → ℂ) :=
  (DeltaLOneFamilyCompleteness.duqlEquiv (fermionFlavor q l)).trans
    (FlavoredCyclicSelection.duqlResidualEquiv (fun _ : Fin 5 => Fin 3)
      (InverseCyclicSMCharges.universal q l))

def base (c : DressedDuqlFamily.Indices q l → ℂ) := (baseEquiv q l).symm c

theorem base_injective : Function.Injective (base q l) := (baseEquiv q l).symm.injective

/-- Same certified scalar coefficient, reindexed to balanced total degree. -/
def balancedScalar (r : ℕ) : IntertwiningMap
    ((BnvMixedInput.scalarRepresentation (scalarFlavor (k := k))).symmetricPower (r+r))
    (trivial ℂ ((StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × CyclicCharge.Group k) ℂ) := by
  have e : r*2 = r+r := by omega
  exact e ▸ (NeutralHiggsPowers.normalized (H := CyclicCharge.Group k) r)

omit [NeZero k] in
theorem balancedScalar_nonzero (r : ℕ) : balancedScalar (k := k) r ≠ 0 := by
  let T (n : ℕ) := IntertwiningMap
    ((NeutralHiggsPowers.action (H := CyclicCharge.Group k)).symmetricPower n)
    (trivial ℂ (NeutralHiggsPowers.G (CyclicCharge.Group k)) ℂ)
  have transport (n m : ℕ) (e : n = m) (f : T n) (hn : f ≠ 0) :
      (e ▸ f : T m) ≠ 0 := by
    subst m
    exact hn
  exact transport (r*2) (r+r) (by omega) _
    (NeutralHiggsPowers.normalized_nonzero r)

def rawDress (r : ℕ) (c : DressedDuqlFamily.Indices q l → ℂ) :
    BnvMixedInput.Coefficient (fermionFlavor q l) scalarFlavor 4 (r+r) :=
  MixedInvariantDressing.product (base q l c).val (balancedScalar r)

theorem rawDress_value (r : ℕ) (c : DressedDuqlFamily.Indices q l → ℂ)
    (p : Fin 4 → Species) (s : Fin (r+r) → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) (s j)) :
    BnvMixedInput.value (fermionFlavor q l) scalarFlavor (rawDress q l r c) p s v w =
      FiniteSpeciesExterior.restrict (DeltaLOneSignedFields.field (fermionFlavor q l))
        (base q l c).val p v *
      balancedScalar (k := k) r (SymmetricPower.tprod ℂ (fun j => Pi.single (s j) (w j))) := by
  exact MixedInvariantDressing.product_apply _ _ _ _

theorem rawDress_mem (r : ℕ) (c : DressedDuqlFamily.Indices q l → ℂ) :
    rawDress q l r c ∈ Space (fermionFlavor q l) scalarFlavor r r := by
  intro p s hs v w
  change BnvMixedInput.value (fermionFlavor q l) scalarFlavor (rawDress q l r c) p s v w = 0
  by_contra hn
  have hp : counts p = DeltaLOneSpeciesSupport.duql := by
    by_contra hp
    have hz := (base q l c).property p hp
    rw [rawDress_value, hz] at hn
    exact hn (by simp)
  have hy := BnvMixedInput.hypercharge_of_nonzero (fermionFlavor q l) scalarFlavor
    (rawDress q l r c) p s v w hn
  rw [← hypercharge_counts, hp, scalar_hypercharge] at hy
  norm_num [DeltaLOneSpeciesSupport.sixHypercharge, DeltaLOneSpeciesSupport.duql] at hy
  have ht := scalarCount_total s
  exact hs ⟨hp, by omega, by omega⟩

def dressed (r : ℕ) (c : DressedDuqlFamily.Indices q l → ℂ) : CyclicSpace q l r r :=
  ⟨rawDress q l r c, rawDress_mem q l r c⟩

theorem dressed_nonzero (r : ℕ) (c : DressedDuqlFamily.Indices q l → ℂ) (hc : c ≠ 0) :
    dressed q l r c ≠ 0 := by
  intro hz
  have hb : (base q l c).val ≠ 0 := by
    intro hh
    apply hc
    apply base_injective q l
    apply Subtype.ext
    have hb0 : base q l 0 = 0 := by
      exact (baseEquiv q l).symm.map_zero
    rw [hb0]
    exact hh
  exact MixedInvariantDressing.product_nonzero _ _ hb (balancedScalar_nonzero r)
    (congrArg Subtype.val hz)

/-- Support of the whole actual fixed-content space, without a spanning premise. -/
theorem allowed_iff (h a : ℕ) : SelectionCriteria.Allowed (CyclicSpace q l h a) ↔
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
    exact ⟨balance_of_nonzero _ _ h a f p s v w hn,
      charge_of_nonzero q l h a f p s v w hn⟩
  · rintro ⟨rfl,hz⟩
    obtain ⟨i⟩ := (DressedDuqlFamily.indices_nonempty_iff q l).mpr hz
    let c : DressedDuqlFamily.Indices q l → ℂ := fun _ => 1
    have hc : c ≠ 0 := by intro hh; have hi := congrFun hh i; norm_num [c] at hi
    exact ⟨dressed q l h c, dressed_nonzero q l h c hc⟩

theorem forbidden_iff (h a : ℕ) : SelectionCriteria.Forbidden (CyclicSpace q l h a) ↔
    h ≠ a ∨ 3*q+l ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, allowed_iff]
  exact not_and_or


/-- Exact all-Higgs prohibition for this content only. -/
theorem all_forbidden_iff : (∀ h a, SelectionCriteria.Forbidden (CyclicSpace q l h a)) ↔
    3*q+l ≠ 0 := by
  constructor
  · intro hh
    have h0 := (forbidden_iff q l 0 0).mp (hh 0 0)
    exact h0.resolve_left (by simp)
  · intro hz h a
    exact (forbidden_iff q l h a).mpr (Or.inr hz)

end Cyclic
end Physics.DuqlHiggsContent
