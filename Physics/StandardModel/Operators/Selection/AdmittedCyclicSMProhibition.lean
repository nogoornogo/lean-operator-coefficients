import Math.RepresentationTheory.Protection.AdmittedCyclicProhibition
import Physics.StandardModel.Operators.Selection.ProhibitionInputSM
import Physics.StandardModel.Operators.Selection.InverseLeptonParitySelection

namespace Physics.AdmittedCyclicSMProhibition
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput SelectionCriteria
variable {k : ℕ} [NeZero k] {F : Species → Type*}
  [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
  (flavor : ∀ u, Representation ℂ (CyclicCharge.Group k) (F u))
  (scalarFlavor : ∀ u, Representation ℂ (CyclicCharge.Group k) (S u))
  (fq : Species → ZMod k) (bq : BnvMixedInput.ScalarSpecies → ZMod k)
  (hf : ∀ g u v, flavor u g v = MixedChargeSelection.cyclicCharacter g (fq u) • v)
  (hb : ∀ g u v, scalarFlavor u g v = MixedChargeSelection.cyclicCharacter g (bq u) • v)

include hf hb in
theorem forbidden_iff (t : ℤ × ℤ → Prop) (n m : ℕ) :
    ProhibitionInputSM.Forbids flavor scalarFlavor t n m ↔
    ∀ x : GradedMixedCompleteness.Content (P := Species) (Q := BnvMixedInput.ScalarSpecies) n m,
      (ComposableBLSupport.specification t).test n m x.out.1 x.out.2 →
      Nontrivial (TypedMixedSeparatedHom.Carrier DeltaLOneSignedFields.localField
        GradedBnvComparison.scalarLocal flavor scalarFlavor x.out.1 x.out.2) →
      MixedChargeSelection.charge fq bq x.out.1 x.out.2 ≠ 0 := by
  rw [ProhibitionInputSM.facade_iff]
  exact AdmittedCyclicProhibition.forbidden_iff _ _ _ _ fq bq hf hb _ n m

include hf hb in
theorem all_forbidden_iff (t : ℤ × ℤ → Prop) :
    ProhibitionInputSM.AllForbids flavor scalarFlavor t ↔
    ∀ n m, ∀ x : GradedMixedCompleteness.Content (P := Species) (Q := BnvMixedInput.ScalarSpecies) n m,
      (ComposableBLSupport.specification t).test n m x.out.1 x.out.2 →
      Nontrivial (TypedMixedSeparatedHom.Carrier DeltaLOneSignedFields.localField
        GradedBnvComparison.scalarLocal flavor scalarFlavor x.out.1 x.out.2) →
      MixedChargeSelection.charge fq bq x.out.1 x.out.2 ≠ 0 := by
  unfold ProhibitionInputSM.AllForbids
  simp only [forbidden_iff flavor scalarFlavor fq bq hf hb]

/-- Odd fermion degree has no actual coefficients, regardless of residual charges. -/
theorem odd_coefficients_zero {R : Type*} [Group R]
    (a : ∀ u, Representation ℂ R (F u))
    (b : ∀ u, Representation ℂ R (S u)) (n m : ℕ) (hn : n % 2 ≠ 0) :
    Forbidden (BnvMixedInput.Coefficient a b n m) := by
  intro f
  apply BnvMixedInput.value_ext a b
  intro p s v w
  by_contra h
  exact hn (BnvMixedInput.even_fermions_of_nonzero a b f p s v w h)

def tripleQ : Fin 3 → Species := fun _ => 0

theorem neutral_b1_content :
    (∑ i, baryon (tripleQ i)).natAbs = 3 ∧
    InverseLeptonParitySelection.total tripleQ (Fin.elim0 : Fin 0 → BnvMixedInput.ScalarSpecies) = 0 := by
  simp [tripleQ,InverseLeptonParitySelection.total_lepton,baryon,lepton]

/-- All-degree B1 prohibition does not require detecting every raw B1 content. -/
theorem raw_filter_not_necessary :
    ProhibitionInputSM.AllForbids
      (InverseLeptonParitySelection.flavor (F := F))
      (InverseLeptonParitySelection.scalarFlavor (S := S)) InverseLeptonParitySelection.target ∧
    ¬ (∀ n m (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies),
      (∑ i, baryon (p i)).natAbs = 3 → InverseLeptonParitySelection.total p s ≠ 0) := by
  refine ⟨InverseLeptonParitySelection.all_forbidden, ?_⟩
  intro h
  exact h 3 0 tripleQ Fin.elim0 neutral_b1_content.1 neutral_b1_content.2
end
end Physics.AdmittedCyclicSMProhibition
