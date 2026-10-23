import Physics.StandardModel.Operators.Support.Joint.SMSignedHiggsSupport
import Math.RepresentationTheory.Content.PatternSpeciesRestriction

/-! Conjugation of arbitrary actual mixed statistical contents, including the
weak Higgs degree and exact hypercharge reversal. Residual actions are not
identified by this local equivalence. -/
namespace Physics.SMMixedConjugation
set_option autoImplicit false
noncomputable section
open Math Representation SMIntegralLocalWeights SMLowerHiggsSupport
open scoped TensorProduct

def oppositeEquiv : DeltaLOneSignedInput.Species ≃ DeltaLOneSignedInput.Species :=
  BnvLocalConjugation.opposite_involutive.toPerm BnvLocalConjugation.opposite

variable {H : Type*} [_root_.Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def sourceEquiv : Representation.Equiv (SMIntegralLocalWeights.source flavor p)
    ((SMIntegralLocalWeights.source flavor (BnvLocalConjugation.opposite ∘ p)).comp
      BnvLocalConjugation.conjugate) :=
  PatternSpeciesRestriction.equiv (DeltaLOneSignedFields.field flavor)
    (DeltaLOneSignedFields.field flavor) oppositeEquiv (MonoidHom.inl Group H)
    ((MonoidHom.inl Group H).comp BnvLocalConjugation.conjugate)
    (SMSignedHiggsSupport.fieldEquiv flavor) p

def actionEquiv (m : ℕ) (delta : ℤ) : Representation.Equiv
    (SMIntegralLocalWeights.action flavor p m delta)
    ((SMIntegralLocalWeights.action flavor (BnvLocalConjugation.opposite ∘ p) m (-delta)).comp
      BnvLocalConjugation.conjugate) :=
  BnvLocalConjugation.tensor (sourceEquiv flavor p) (SMSignedHiggsSupport.bosonEquiv (H := H) m delta)

def coefficientEquiv (m : ℕ) (delta : ℤ) :
    InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta) ≃ₗ[ℂ]
    InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor (BnvLocalConjugation.opposite ∘ p) m (-delta)) :=
  (InvariantCoefficientTransport.alongEquiv (actionEquiv flavor p m delta)).trans
    (InvariantCoefficientTransport.alongSurjection _ _ BnvLocalConjugation.surjective)

omit flavor in
theorem bound_eq : SMContentWeakBound.bound p =
    SMContentWeakBound.bound (BnvLocalConjugation.opposite ∘ p) := by
  apply Finset.sum_congr rfl
  intro i _
  have h := SMSignedHiggsSupport.opposite_bound (p i) 1
  simpa [SMContentWeakBound.bound, SMLowerGenerationSupport.pattern,
    SMConstantWeakCapacity.pattern] using h

theorem local_higgs_transport (h d : ℕ) (ha : LocalHiggs flavor p h d) :
    LocalHiggs flavor (BnvLocalConjugation.opposite ∘ p) d h := by
  obtain ⟨m,hm,ha⟩ := ha
  refine ⟨⟨m.val,by rw [← bound_eq]; exact m.isLt⟩,?_,?_⟩
  · dsimp [BoundedHiggsSupport.Admissible] at hm ⊢
    omega
  · have ht := (SelectionCriteria.allowed_equiv
      (coefficientEquiv flavor p m.val ((h : ℤ)-d))).mp ha
    have he : -((h : ℤ)-d)=(d : ℤ)-h := by ring
    rwa [he] at ht

theorem local_higgs_iff (h d : ℕ) : LocalHiggs flavor p h d ↔
    LocalHiggs flavor (BnvLocalConjugation.opposite ∘ p) d h := by
  refine ⟨local_higgs_transport flavor p h d,?_⟩
  intro ha
  have ht := local_higgs_transport flavor (BnvLocalConjugation.opposite ∘ p) d h ha
  have he : BnvLocalConjugation.opposite ∘ (BnvLocalConjugation.opposite ∘ p)=p := by
    funext i
    exact BnvLocalConjugation.opposite_involutive _
  rwa [he] at ht

variable {k : ℕ} [NeZero k] (q l : ZMod k)

omit flavor p [NeZero k] in
theorem signed_charge_opposite (s : DeltaLOneSignedInput.Species) :
    DuqlHiggsContent.signedCharge q l (BnvLocalConjugation.opposite s) =
      -DuqlHiggsContent.signedCharge q l s := by
  fin_cases s <;> simp [DuqlHiggsContent.signedCharge, BnvLocalConjugation.opposite]

omit flavor [NeZero k] in
theorem charge_opposite : QLFiniteSupport.charge q l (BnvLocalConjugation.opposite ∘ p) =
    -QLFiniteSupport.charge q l p := by
  simp only [QLFiniteSupport.charge, Function.comp_apply, signed_charge_opposite,
    Finset.sum_neg_distrib]

omit flavor in
theorem original_ql_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l) p h d) ↔
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (QLFiniteSupport.flavor q l)
      (BnvLocalConjugation.opposite ∘ p) d h) := by
  rw [SMLowerHiggsSupport.ql_original_iff, SMLowerHiggsSupport.ql_original_iff,
    charge_opposite, neg_eq_zero]
  exact and_congr_right (fun _ => local_higgs_iff (QLFiniteSupport.flavor q l) p h d)

end
end Physics.SMMixedConjugation
