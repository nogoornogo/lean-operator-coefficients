import Physics.StandardModel.Operators.SMContentWeakBound
import Physics.StandardModel.Operators.FullHiggsCoefficientBridge
import Math.RepresentationTheory.BoundedHiggsSupport
import Math.RepresentationTheory.PatternCoefficientSupport
import Math.RepresentationTheory.InvariantTensorCharge

/-! Finite Higgs support reduction with residual flavor actions as parameters. -/
namespace GUT.SMFiniteHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation BoundedHiggsSupport
open scoped TensorProduct
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

abbrev source := SMContentWeakBound.source flavor p
abbrev Test (m : ℕ) (delta : ℤ) := BoundedHiggsSupport.Test (source flavor p)
  SMHiggsConstituents.weakProjection SMHiggsConstituents.character m delta
abbrev Space (h d : ℕ) := FullHiggsCoefficientBridge.Space (source flavor p) h d

theorem weak_projection (u : WeakDoubletScalars.Group) :
    SMHiggsConstituents.weakProjection (WeakSingletHiggsSupport.weakInclusion (H := H) u) = u := rfl
theorem weak_character (u : WeakDoubletScalars.Group) :
    SMHiggsConstituents.character (WeakSingletHiggsSupport.weakInclusion (H := H) u) = 1 := by
  apply Units.ext
  simp [SMHiggsConstituents.character_apply, WeakSingletHiggsSupport.weakInclusion,
    StandardSMGaugeTensor.phase]

theorem source_bound : BoundedTorusWeights.Bounded
    ((source flavor p).comp (WeakSingletHiggsSupport.weakInclusion (H := H)))
    TauCeti.SU2.torusHom (SMContentWeakBound.bound p) :=
  SMContentWeakBound.source_bounded flavor p

theorem split_allowed (h d : ℕ) : SelectionCriteria.Allowed (Space flavor p h d) ↔
    SelectionCriteria.Allowed (BoundedHiggsSupport.Space (source flavor p)
      SMHiggsConstituents.weakProjection SMHiggsConstituents.character h d) := by
  have hb : SMHiggsConstituents.Bosons (H := H) h d =
      TwistedSU2ClebschGordan.Bosons SMHiggsConstituents.weakProjection
        SMHiggsConstituents.character h d := by
    unfold SMHiggsConstituents.Bosons
    rw [SMHiggsConstituents.higgs_eq]
  refine (SelectionCriteria.allowed_equiv
    (FullHiggsCoefficientBridge.splitEquiv (source flavor p) h d)).trans ?_
  change SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants
    ((source flavor p).tprod (SMHiggsConstituents.Bosons h d))) ↔ _
  rw [hb]

theorem finite_allowed_iff (h d : ℕ) : SelectionCriteria.Allowed (Space flavor p h d) ↔
    ∃ m : Fin (SMContentWeakBound.bound p+1), Admissible h d m.val ∧
      SelectionCriteria.Allowed (Test flavor p m.val ((h : ℤ)-d)) :=
  (split_allowed flavor p h d).trans
    (BoundedHiggsSupport.finite_allowed_iff (source flavor p)
      SMHiggsConstituents.weakProjection SMHiggsConstituents.character
      WeakSingletHiggsSupport.weakInclusion weak_projection weak_character
      (SMContentWeakBound.bound p) (source_bound flavor p) h d)

abbrev Scalars := FiniteSpeciesExterior.representation
  (BnvMixedInput.scalarField (NeutralHiggsPowers.flavor (H := H)))
abbrev FullSource := PatternExteriorSource.Full (DeltaLOneSignedFields.field flavor) (n := n)

def OriginalSpace (h d : ℕ) : Submodule ℂ
    (InvariantCoefficientTransport.Invariants ((FullSource flavor (n := n)).tprod
      ((Scalars (H := H)).symmetricPower (h+d)))) where
  carrier := {f | f ∈ FullHiggsCoefficientBridge.Space (FullSource flavor (n := n)) h d ∧
    PatternCoefficientSupport.Supported (DeltaLOneSignedFields.field flavor) p
      ((Scalars (H := H)).symmetricPower (h+d)) f}
  zero_mem' := ⟨(FullHiggsCoefficientBridge.Space _ h d).zero_mem,
    (PatternCoefficientSupport.space (DeltaLOneSignedFields.field flavor) p
      ((Scalars (H := H)).symmetricPower (h+d))).zero_mem⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨Submodule.add_mem _ hf.1 hg.1,
      (PatternCoefficientSupport.space (DeltaLOneSignedFields.field flavor) p
        ((Scalars (H := H)).symmetricPower (h+d))).add_mem hf.2 hg.2⟩
  smul_mem' := by
    intro z f hf
    exact ⟨Submodule.smul_mem _ z hf.1,
      (PatternCoefficientSupport.space (DeltaLOneSignedFields.field flavor) p
        ((Scalars (H := H)).symmetricPower (h+d))).smul_mem z hf.2⟩

def originalEquiv (h d : ℕ) : OriginalSpace flavor p h d ≃ₗ[ℂ] Space flavor p h d where
  toFun f := ⟨PatternCoefficientSupport.restrict _ p _ f.val, by
    rw [FullHiggsCoefficientBridge.mem_space_iff]
    intro labels hwrong v x
    have hf := (FullHiggsCoefficientBridge.mem_space_iff _ h d f.val).mp f.property.1
    exact hf labels hwrong v x.val⟩
  invFun f := ⟨PatternCoefficientSupport.extend _ p _ f.val, by
    refine ⟨?_, PatternCoefficientSupport.extend_supported _ p _ f.val⟩
    rw [FullHiggsCoefficientBridge.mem_space_iff]
    intro labels hwrong v x
    have hf := (FullHiggsCoefficientBridge.mem_space_iff _ h d f.val).mp f.property
    exact hf labels hwrong v (PatternExteriorSource.projectionLinear _ p x)⟩
  left_inv f := Subtype.ext (PatternCoefficientSupport.extend_restrict _ p _ ⟨f.val,f.property.2⟩)
  right_inv f := Subtype.ext (PatternCoefficientSupport.restrict_extend _ p _ f.val)
  map_add' _ _ := by apply Subtype.ext; ext x y; rfl
  map_smul' _ _ := by apply Subtype.ext; ext x y; rfl

theorem mem_original_iff (h d : ℕ)
    (f : InvariantCoefficientTransport.Invariants ((FullSource flavor (n := n)).tprod
      ((Scalars (H := H)).symmetricPower (h+d)))) :
    f ∈ OriginalSpace flavor p h d ↔
      (∀ labels : Fin (h+d) → BnvMixedInput.ScalarSpecies,
        ((Finset.univ.filter (fun i => labels i = 0)).card ≠ h ∨
          (Finset.univ.filter (fun i => labels i = 1)).card ≠ d) →
        ∀ (v : ∀ i, BnvMixedInput.ScalarField (S := NeutralHiggsPowers.Multiplicity) (labels i)) x,
          f (x ⊗ₜ[ℂ] SymmetricPower.tprod ℂ
          (fun i => Pi.single (labels i) (v i))) = 0) ∧
      (∀ labels : Fin n → DeltaLOneSignedInput.Species,
        (¬ ∀ s, (Finset.univ.filter (fun i => labels i = s)).card =
          (Finset.univ.filter (fun i => p i = s)).card) →
        ∀ (v : ∀ i, DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) (labels i)) y,
          f (exteriorPower.ιMulti ℂ n
          (fun i => Pi.single (labels i) (v i)) ⊗ₜ[ℂ] y) = 0) := by
  change (_ ∧ PatternCoefficientSupport.Supported _ p _ f) ↔ _
  rw [FullHiggsCoefficientBridge.mem_space_iff]
  simp only [PatternCoefficientSupport.Supported, PatternExteriorSource.orbit_iff_counts]

theorem original_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (OriginalSpace flavor p h d) ↔
    ∃ m : Fin (SMContentWeakBound.bound p+1), Admissible h d m.val ∧
      SelectionCriteria.Allowed (Test flavor p m.val ((h : ℤ)-d)) :=
  (SelectionCriteria.allowed_equiv (originalEquiv flavor p h d)).trans
    (finite_allowed_iff flavor p h d)

theorem original_table_iff (h d : ℕ) :
    SelectionCriteria.Allowed (OriginalSpace flavor p h d) ↔
      ∃ s t : Fin (SMContentWeakBound.bound p+1), s.val+t.val ≤ SMContentWeakBound.bound p ∧
        (h : ℤ)-d = (s.val : ℤ)-t.val ∧ Admissible h d (s.val+t.val) ∧
        SelectionCriteria.Allowed (Test flavor p (s.val+t.val) ((s.val : ℤ)-t.val)) :=
  (SelectionCriteria.allowed_equiv (originalEquiv flavor p h d)).trans
    ((split_allowed flavor p h d).trans
      (BoundedHiggsSupport.finite_table_iff (source flavor p)
        SMHiggsConstituents.weakProjection SMHiggsConstituents.character
        WeakSingletHiggsSupport.weakInclusion weak_projection weak_character
        _ (source_bound flavor p) h d))

theorem original_pair_monotone (h d : ℕ) :
    SelectionCriteria.Allowed (OriginalSpace flavor p h d) →
      SelectionCriteria.Allowed (OriginalSpace flavor p (h+1) (d+1)) := by
  intro hh
  have hi := (SelectionCriteria.allowed_equiv (originalEquiv flavor p h d)).mp hh
  have hs := (split_allowed flavor p h d).mp hi
  have ht := BoundedHiggsSupport.pair_monotone (source flavor p)
    SMHiggsConstituents.weakProjection SMHiggsConstituents.character
    WeakSingletHiggsSupport.weakInclusion weak_projection weak_character
    _ (source_bound flavor p) h d hs
  exact (SelectionCriteria.allowed_equiv (originalEquiv flavor p (h+1) (d+1))).mpr
    ((split_allowed flavor p (h+1) (d+1)).mpr ht)

theorem original_pair_stable (h d : ℕ)
    (hdelta : (h-d)+(d-h) ≤ SMContentWeakBound.bound p)
    (ht : (SMContentWeakBound.bound p-((h-d)+(d-h)))/2 ≤ min h d) :
    SelectionCriteria.Allowed (OriginalSpace flavor p (h+1) (d+1)) ↔
      SelectionCriteria.Allowed (OriginalSpace flavor p h d) := by
  have e1 := (SelectionCriteria.allowed_equiv (originalEquiv flavor p (h+1) (d+1))).trans
    (split_allowed flavor p (h+1) (d+1))
  have e2 := (SelectionCriteria.allowed_equiv (originalEquiv flavor p h d)).trans
    (split_allowed flavor p h d)
  have es := BoundedHiggsSupport.pair_stable_at_threshold (source flavor p)
    SMHiggsConstituents.weakProjection SMHiggsConstituents.character
    WeakSingletHiggsSupport.weakInclusion weak_projection weak_character
    (SMContentWeakBound.bound p) (source_bound flavor p) h d hdelta ht
  exact e1.trans (es.trans e2.symm)

theorem original_imbalance_forbidden (h d : ℕ)
    (hbad : SMContentWeakBound.bound p < (h-d)+(d-h)) :
    SelectionCriteria.Forbidden (OriginalSpace flavor p h d) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, original_allowed_iff]
  rintro ⟨m,hm,ht⟩
  have hn := m.isLt
  dsimp [Admissible] at hm
  omega

theorem original_degree_forbidden (h d : ℕ) (hn : 180 < n) :
    SelectionCriteria.Forbidden (OriginalSpace flavor p h d) := by
  intro f
  apply Subtype.ext
  exact ThreeGenerationFermionBound.coefficients_zero flavor NeutralHiggsPowers.flavor
    n (h+d) hn f.val

theorem constituent_hypercharge (m : ℕ) (delta : ℤ) (z : Circle)
    (v : Sym[ℂ]^m WeakDoubletScalars.Doublet) :
    BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta (DeltaLOneSignedFields.fullHypercharge (R := H) z) v =
    (z : ℂ)^(3*delta) • v := by
  change ((SMHiggsConstituents.character^delta)
      (DeltaLOneSignedFields.fullHypercharge (R := H) z) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) 1 v = _
  simp only [map_one, Module.End.one_apply, MonoidHom.zpow_apply, Units.smul_def,
    Units.val_zpow_eq_zpow_val, SMHiggsConstituents.character_apply]
  have hp : StandardSMGaugeTensor.phase 3
      (DeltaLOneSignedFields.hyperchargeElement z) = (z : ℂ)^(3 : ℤ) := rfl
  change (StandardSMGaugeTensor.phase 3 (DeltaLOneSignedFields.hyperchargeElement z))^delta • v = _
  rw [hp, ← zpow_mul]

theorem test_charge (m : ℕ) (delta : ℤ)
    (ht : SelectionCriteria.Allowed (Test flavor p m delta)) :
    SMContentWeakBound.hypercharge p + 3*delta = 0 :=
  InvariantTensorCharge.charge_zero (source flavor p)
    (BoundedHiggsSupport.constituent (SMHiggsConstituents.weakProjection (H := H))
      SMHiggsConstituents.character m delta)
    DeltaLOneSignedFields.fullHypercharge (SMContentWeakBound.hypercharge p) (3*delta)
    (SMContentWeakBound.source_hypercharge flavor p) (constituent_hypercharge m delta) ht

theorem original_charge_finite_iff (h d : ℕ) :
    SelectionCriteria.Allowed (OriginalSpace flavor p h d) ↔
    SMContentWeakBound.hypercharge p + 3*((h : ℤ)-d) = 0 ∧
      ∃ m : Fin (SMContentWeakBound.bound p+1), Admissible h d m.val ∧
        SelectionCriteria.Allowed (Test flavor p m.val ((h : ℤ)-d)) := by
  rw [original_allowed_iff]
  constructor
  · intro hh
    obtain ⟨m,hm,ht⟩ := hh
    exact ⟨test_charge flavor p _ _ ht, m,hm,ht⟩
  · exact And.right

theorem original_forbidden_iff (h d : ℕ) :
    SelectionCriteria.Forbidden (OriginalSpace flavor p h d) ↔
    ¬ (SMContentWeakBound.hypercharge p + 3*((h : ℤ)-d) = 0 ∧
      ∃ m : Fin (SMContentWeakBound.bound p+1), Admissible h d m.val ∧
        SelectionCriteria.Allowed (Test flavor p m.val ((h : ℤ)-d))) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, original_charge_finite_iff]

theorem original_pairs_stable (h d r : ℕ)
    (hdelta : (h-d)+(d-h) ≤ SMContentWeakBound.bound p)
    (ht : (SMContentWeakBound.bound p-((h-d)+(d-h)))/2 ≤ min h d) :
    SelectionCriteria.Allowed (OriginalSpace flavor p (h+r) (d+r)) ↔
      SelectionCriteria.Allowed (OriginalSpace flavor p h d) := by
  have hs : SMContentWeakBound.bound p ≤ h+d+1 := by
    rcases Nat.le_total h d with hh | hh
    · rw [Nat.min_eq_left hh] at ht; omega
    · rw [Nat.min_eq_right hh] at ht; omega
  have e1 := (SelectionCriteria.allowed_equiv (originalEquiv flavor p (h+r) (d+r))).trans
    (split_allowed flavor p (h+r) (d+r))
  have e2 := (SelectionCriteria.allowed_equiv (originalEquiv flavor p h d)).trans
    (split_allowed flavor p h d)
  have es := BoundedHiggsSupport.pairs_stable (source flavor p)
    SMHiggsConstituents.weakProjection SMHiggsConstituents.character
    WeakSingletHiggsSupport.weakInclusion weak_projection weak_character
    (SMContentWeakBound.bound p) (source_bound flavor p) h d hs r
  exact e1.trans (es.trans e2.symm)

end
end GUT.SMFiniteHiggsSupport
