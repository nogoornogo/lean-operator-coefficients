import Physics.FieldTheory.Jets.Weyl.Higgs.WeylHiggsCurrent
import Physics.FieldTheory.Jets.Scalar.Inputs.DerivativeLiteratureRecheck

/-! Every generated equation is compared with the actual component seed.
The equality transports full unbounded closures, not only a finite list of rows. -/
namespace Physics.WeylHiggsRelations
set_option autoImplicit false
noncomputable section
open Math Math.JetLinear PairedWeylKinetic WeylHiggsInput

@[reducible] local instance : AddCommGroup A := inferInstance
@[reducible] local instance : Module ℂ A := inferInstance
@[reducible] local instance : Ring A := inferInstance

def componentSeed : Label ⊕ Label → A := Sum.elim seed
  (fun j => scalarEmbed (DerivativeLiteratureHiggs.seed 0 0 j))
def generatedSeed : Label ⊕ Label → A := Sum.elim
  (fun j => density.euler (.inl (!j.1,j.2)))
  (fun j => scalarEmbed ((Math.HiggsLagrangianInput.density 0 0).scalarEuler (!j.1,j.2)))

theorem generated_odd (j : Label) : generatedSeed (.inl j) = componentSeed (.inl j) := by
  simp [generatedSeed, componentSeed, PairedWeylKinetic.generated_odd]
theorem generated_even (j : Label) : generatedSeed (.inr j) = -componentSeed (.inr j) := by
  simp [generatedSeed, componentSeed, Math.HiggsLagrangianInput.generated_equation]

theorem component_span : Submodule.span ℂ (Set.range componentSeed) =
    Submodule.span ℂ equations := by
  have hr : Set.range componentSeed = seeds ∪ scalarEmbed '' DerivativeLiteratureHiggs.seeds 0 0 := by
    ext p
    constructor
    · rintro ⟨j,rfl⟩
      cases j with
      | inl j => exact Or.inl ⟨j,rfl⟩
      | inr j => exact Or.inr ⟨_,⟨j,rfl⟩,rfl⟩
    · rintro (⟨j,rfl⟩ | ⟨_,⟨j,rfl⟩,rfl⟩)
      · exact ⟨.inl j,rfl⟩
      · exact ⟨.inr j,rfl⟩
  rw [hr, equations, Submodule.span_union, Submodule.span_union, PairedWeylInput.equation_span]

theorem generated_span : Submodule.span ℂ (Set.range generatedSeed) =
    Submodule.span ℂ (Set.range componentSeed) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨j,rfl⟩
    cases j with
    | inl j => rw [generated_odd]; exact Submodule.subset_span ⟨_,rfl⟩
    | inr j => rw [generated_even]; exact Submodule.neg_mem _ (Submodule.subset_span ⟨_,rfl⟩)
  · rintro _ ⟨j,rfl⟩
    cases j with
    | inl j => rw [← generated_odd]; exact Submodule.subset_span ⟨_,rfl⟩
    | inr j =>
      have he : componentSeed (.inr j) = -generatedSeed (.inr j) := by
        rw [generated_even, neg_neg]
      rw [he]
      exact Submodule.neg_mem _ (Submodule.subset_span ⟨_,rfl⟩)

theorem component_closure : TwoSidedDifferential.relations D (Set.range componentSeed) =
    TwoSidedDifferential.relations D equations :=
  TwoSidedDifferential.relations_eq_of_span D component_span

theorem generated_relations : TwoSidedDifferential.combined D (Set.range generatedSeed) =
    input.relations := by
  change TwoSidedDifferential.relations D (Set.range generatedSeed) ⊔ _ =
    TwoSidedDifferential.relations D equations ⊔ _
  rw [TwoSidedDifferential.relations_eq_of_span D (generated_span.trans component_span)]

def generated : DerivativeInterface.Input Group A where
  action := action
  relations := TwoSidedDifferential.combined D (Set.range generatedSeed)
  stable g := by rw [generated_relations]; exact stable g

def coefficientEquiv : generated.Coefficient ≃ₗ[ℂ] input.Coefficient where
  toFun f := ⟨f.val, by
    intro p hp
    apply f.property
    change p ∈ TwoSidedDifferential.combined D (Set.range generatedSeed)
    rw [generated_relations]
    exact hp⟩
  invFun f := ⟨f.val, by
    intro p hp
    apply f.property
    change p ∈ TwoSidedDifferential.combined D (Set.range generatedSeed) at hp
    rw [generated_relations] at hp
    exact hp⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem extraction (f : generated.Coefficient) (p : A) :
    (coefficientEquiv f).val p = f.val p := rfl

theorem paired_relations : TwoSidedDifferential.relations D seeds ≤
    TwoSidedDifferential.relations D equations := by
  rw [← PairedWeylInput.closure_equal]
  apply TwoSidedDifferential.minimal
  · exact fun _ hp => TwoSidedDifferential.seed_mem _ _ (Or.inl hp)
  · exact fun a p hp => TwoSidedDifferential.left_mem _ _ a hp
  · exact fun a p hp => TwoSidedDifferential.right_mem _ _ a hp
  · exact fun i p hp => TwoSidedDifferential.derivative_mem _ _ i hp

theorem conserved_products (f : input.Coefficient) (p q : A) :
    f.val (p*DerivativeLiteratureRecheck.C5.currentDivergence*q) = 0 := by
  apply f.property
  exact Submodule.mem_sup_left (TwoSidedDifferential.right_mem _ _ _
    (TwoSidedDifferential.left_mem _ _ _ (paired_relations DerivativeLiteratureRecheck.C5.divergence_eom)))

theorem current_ibp (f : input.Coefficient) (i : Fin 4) (p q : A) :
    f.val (p*D i q) = -f.val (D i p*q) := by
  have hm : D i (p*q) ∈ input.relations :=
    Submodule.mem_sup_right ⟨Finsupp.single i (p*q),VariationalIBP.divergence_single D i (p*q)⟩
  have hz := f.property hm
  change f.val (D i (p*q)) = 0 at hz
  rw [MixedJetAlgebra.totalDerivative_mul,map_add] at hz
  exact eq_neg_of_add_eq_zero_right hz

theorem symmetric_current_zero (f : input.Coefficient) (p : A) :
    f.val (∑ i : Fin 4, DerivativeLiteratureMixed.current i * D i p) = 0 := by
  have he : f.val (∑ i : Fin 4, DerivativeLiteratureMixed.current i * D i p) =
      -f.val (DerivativeLiteratureRecheck.C5.currentDivergence*p) := by
    simp only [map_sum,current_ibp,Finset.sum_neg_distrib,
      DerivativeLiteratureRecheck.C5.currentDivergence,Finset.sum_mul]
  rw [he]
  have hz := conserved_products f 1 p
  simpa only [one_mul,neg_zero] using congrArg Neg.neg hz

end
end Physics.WeylHiggsRelations
