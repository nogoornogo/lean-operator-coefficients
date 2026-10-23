import Physics.StandardModel.Operators.Support.Quark.SMQuarkAllHiggsSupport
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvLocalConjugation

/-! Conjugate statistical sources, with exact hypercharge reversal and no
numerical multiplicity or rank classifier. Residual selection is kept separate. -/
namespace Physics.SMSignedHiggsSupport
set_option autoImplicit false
noncomputable section
open Math Representation SMIntegralLocalWeights SMLowerGenerationSupport SMLowerHiggsSupport
open scoped TensorProduct
variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))

def fieldEquiv (s : DeltaLOneSignedInput.Species) : Representation.Equiv
    ((DeltaLOneSignedFields.field flavor s).comp (MonoidHom.inl Group H))
    (((DeltaLOneSignedFields.field flavor (BnvLocalConjugation.opposite s)).comp (MonoidHom.inl Group H)).comp BnvLocalConjugation.conjugate) where
  toLinearEquiv := TensorProduct.congr (BnvLocalConjugation.localField s).toLinearEquiv
    (LinearEquiv.refl ℂ (Fin 3 → ℂ))
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x v
    change (BnvLocalConjugation.localField s) (DeltaLOneSignedFields.localField s g x) ⊗ₜ[ℂ]
      (flavor s 1 v) =
      DeltaLOneSignedFields.localField (BnvLocalConjugation.opposite s) (BnvLocalConjugation.conjugate g)
        ((BnvLocalConjugation.localField s) x) ⊗ₜ[ℂ] (flavor (BnvLocalConjugation.opposite s) 1 v)
    rw [map_one, map_one]
    exact congrArg (fun x => x ⊗ₜ[ℂ] v) ((BnvLocalConjugation.localField s).isIntertwining _ _ g x)

def sourceEquiv (s : DeltaLOneSignedInput.Species) (n : ℕ) : Representation.Equiv
    (SMIntegralLocalWeights.source flavor (pattern s n))
    ((SMIntegralLocalWeights.source flavor (pattern (BnvLocalConjugation.opposite s) n)).comp
      BnvLocalConjugation.conjugate) :=
  (SplitRepresentationProjection.restrictEquiv
    (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) s n)
      (MonoidHom.inl Group H)).symm.trans
    ((fieldEquiv flavor s).exteriorPower n |>.trans
      (SplitRepresentationProjection.restrictEquiv
        (ConstantPatternExterior.equiv (DeltaLOneSignedFields.field flavor) (BnvLocalConjugation.opposite s) n)
          ((MonoidHom.inl Group H).comp BnvLocalConjugation.conjugate)))

def weakConjugate : Representation.Equiv WeakDoubletScalars.doublet
    (WeakDoubletScalars.doublet.comp (SpecialUnitaryContragredient.conjugate 2)) :=
  SU2DoubletDuality.equivalence.trans (SpecialUnitaryContragredient.dualEquiv 2)

def bosonEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMIntegralLocalWeights.boson (H := H) m delta)
    ((SMIntegralLocalWeights.boson (H := H) m (-delta)).comp BnvLocalConjugation.conjugate) where
  toLinearEquiv := (weakConjugate.symmetricPower m).toLinearEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change (weakConjugate.symmetricPower m)
      (((SMHiggsConstituents.character (H := H) ^ delta) (g,1) : ℂˣ) •
        (WeakDoubletScalars.doublet.symmetricPower m) g.1.2.1 x) =
      ((SMHiggsConstituents.character (H := H) ^ (-delta)) (BnvLocalConjugation.conjugate g,1) : ℂˣ) •
        (WeakDoubletScalars.doublet.symmetricPower m)
          (SpecialUnitaryContragredient.conjugate 2 g.1.2.1) ((weakConjugate.symmetricPower m) x)
    have hc : ((SMHiggsConstituents.character (H := H) ^ delta) (g,1) : ℂˣ) =
        ((SMHiggsConstituents.character (H := H) ^ (-delta)) (BnvLocalConjugation.conjugate g,1) : ℂˣ) := by
      apply Units.ext
      simp [MonoidHom.zpow_apply, SMHiggsConstituents.character_apply,
        BnvLocalConjugation.conjugate, SMGaugeConjugation.conjugate,
        StandardSMGaugeTensor.phase, zpow_neg]
    rw [hc]
    simp only [Units.smul_def, map_smul]
    exact congrArg (fun y => _ • y) ((weakConjugate.symmetricPower m).isIntertwining _ _ g.1.2.1 x)

def actionEquiv (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMIntegralLocalWeights.action flavor (pattern s n) m delta)
    ((SMIntegralLocalWeights.action flavor (pattern (BnvLocalConjugation.opposite s) n) m (-delta)).comp
      BnvLocalConjugation.conjugate) :=
  BnvLocalConjugation.tensor (sourceEquiv flavor s n) (bosonEquiv (H := H) m delta)

def coefficientEquiv (s : DeltaLOneSignedInput.Species) (n m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern s n) m delta) ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (pattern (BnvLocalConjugation.opposite s) n) m (-delta)) :=
  (InvariantCoefficientTransport.alongEquiv (actionEquiv flavor s n m delta)).trans
    (InvariantCoefficientTransport.alongSurjection _ _ BnvLocalConjugation.surjective)

omit flavor in
theorem opposite_bound (s : DeltaLOneSignedInput.Species) (n : ℕ) :
    SMContentWeakBound.bound (pattern s n) =
      SMContentWeakBound.bound (pattern (BnvLocalConjugation.opposite s) n) := by
  apply Finset.sum_congr rfl
  intro i _
  change SMWeakWeightBasis.doubletCount s =
    SMWeakWeightBasis.doubletCount (BnvLocalConjugation.opposite s)
  fin_cases s <;> rfl

theorem local_higgs_transport (s : DeltaLOneSignedInput.Species) (n h d : ℕ)
    (ha : LocalHiggs flavor (pattern s n) h d) :
    LocalHiggs flavor (pattern (BnvLocalConjugation.opposite s) n) d h := by
  obtain ⟨m,hm,ha⟩ := ha
  refine ⟨⟨m.val,by rw [← opposite_bound]; exact m.isLt⟩,?_,?_⟩
  · dsimp [BoundedHiggsSupport.Admissible] at hm ⊢
    omega
  · have ht := (SelectionCriteria.allowed_equiv
      (coefficientEquiv flavor s n m.val ((h : ℤ)-d))).mp ha
    have he : -((h : ℤ)-d)=(d : ℤ)-h := by ring
    rw [he] at ht
    exact ht

theorem local_higgs_iff (s : DeltaLOneSignedInput.Species) (n h d : ℕ) :
    LocalHiggs flavor (pattern s n) h d ↔
      LocalHiggs flavor (pattern (BnvLocalConjugation.opposite s) n) d h := by
  refine ⟨local_higgs_transport flavor s n h d,?_⟩
  intro ha
  have ht := local_higgs_transport flavor (BnvLocalConjugation.opposite s) n d h ha
  simpa only [BnvLocalConjugation.opposite_involutive s] using ht

theorem conjugate_quark_local_iff (n h d : ℕ) :
    LocalHiggs flavor (pattern 5 n) h d ↔ n % 2=0 ∧ n ≤ 24 ∧ -(n : ℤ)+3*((h : ℤ)-d)=0 := by
  rw [local_higgs_iff flavor 5 n h d]
  change LocalHiggs flavor (pattern 0 n) d h ↔ _
  rw [SMQuarkAllHiggsSupport.local_higgs_iff]
  omega

theorem conjugate_lepton_local_iff (n h d : ℕ) :
    LocalHiggs flavor (pattern 8 n) h d ↔ n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d= -(n : ℤ) := by
  rw [local_higgs_iff flavor 8 n h d]
  change LocalHiggs flavor (pattern 3 n) d h ↔ _
  rw [lepton_all_local_iff]
  omega

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor [NeZero k] in
theorem conjugate_quark_charge (n : ℕ) : QLFiniteSupport.charge q l (pattern 5 n) = -(n • q) := by
  simp [QLFiniteSupport.charge, pattern, SMConstantWeakCapacity.pattern, DuqlHiggsContent.signedCharge]

omit flavor [NeZero k] in
theorem conjugate_lepton_charge (n : ℕ) : QLFiniteSupport.charge q l (pattern 8 n) = -(n • l) := by
  simp [QLFiniteSupport.charge, pattern, SMConstantWeakCapacity.pattern, DuqlHiggsContent.signedCharge]

omit flavor in
theorem conjugate_quark_ql_iff (n h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 5 n) h d) ↔
      n • q=0 ∧ n % 2=0 ∧ n ≤ 24 ∧ -(n : ℤ)+3*((h : ℤ)-d)=0 := by
  rw [ql_original_iff, conjugate_quark_charge, neg_eq_zero, conjugate_quark_local_iff]

omit flavor in
theorem conjugate_lepton_ql_iff (n h d : ℕ) :
    SelectionCriteria.Allowed
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 8 n) h d) ↔
      n • l=0 ∧ n % 2=0 ∧ n ≤ 6 ∧ (h : ℤ)-d= -(n : ℤ) := by
  rw [ql_original_iff, conjugate_lepton_charge, neg_eq_zero, conjugate_lepton_local_iff]

omit flavor in
theorem conjugate_quark_ql_forbidden (n h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 5 n) h d) ↔
      n • q ≠ 0 ∨ n % 2 ≠ 0 ∨ 24 < n ∨ -(n : ℤ)+3*((h : ℤ)-d) ≠ 0 := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, conjugate_quark_ql_iff q l n h d]
  simp only [not_and_or, not_le]

omit flavor in
theorem conjugate_lepton_ql_forbidden (n h d : ℕ) :
    SelectionCriteria.Forbidden
      (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) (pattern 8 n) h d) ↔
      n • l ≠ 0 ∨ n % 2 ≠ 0 ∨ 6 < n ∨ (h : ℤ)-d ≠ -(n : ℤ) := by
  rw [SelectionCriteria.forbidden_iff_not_allowed, conjugate_lepton_ql_iff q l n h d]
  simp only [not_and_or, not_le]

end
end Physics.SMSignedHiggsSupport
