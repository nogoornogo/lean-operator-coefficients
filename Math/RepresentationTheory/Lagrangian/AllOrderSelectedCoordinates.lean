import Math.RepresentationTheory.Lagrangian.AllOrderDerivativeCoordinates

/-! Exact selected relations retain cancellations among arbitrary finite
combinations of all full-source rows. No global invariant extension is used. -/
namespace Math.AllOrderDerivativeCoordinates.Presentation
set_option autoImplicit false
noncomputable section
variable {H U ι κ τ : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  {P : DerivativeInterface.Input H U} (C : Presentation (ι := ι) (κ := κ) P)
  (V : Submodule ℂ U) (hV : ∀ g, V ≤ V.comap (P.action g))

def rowCombination : (κ →₀ ℂ) →ₗ[ℂ] U := Finsupp.linearCombination ℂ C.relation

theorem rowCombination_range : C.rowCombination.range = P.relations := by
  rw [rowCombination,Finsupp.range_linearCombination,C.relation_span]

abbrev SelectedRow := {q : κ →₀ ℂ // C.rowCombination q ∈ V}

def selectedRelation (q : C.SelectedRow V) : V := ⟨C.rowCombination q.val,q.property⟩

theorem selectedRelation_span :
    Submodule.span ℂ (Set.range (C.selectedRelation V)) = (P.select V hV).relations := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro u ⟨q,rfl⟩
    change C.rowCombination q.val ∈ P.relations
    rw [← C.rowCombination_range]
    exact ⟨q.val,rfl⟩
  · intro u hu
    change u.val ∈ P.relations at hu
    rw [← C.rowCombination_range] at hu
    obtain ⟨q,hq⟩ := hu
    have hqV : C.rowCombination q ∈ V := hq ▸ u.property
    apply Submodule.subset_span
    refine ⟨⟨q,hqV⟩,?_⟩
    exact Subtype.ext hq

def selectedPresentation (b : Module.Basis τ ℂ V) :
    Presentation (ι := τ) (κ := C.SelectedRow V) (P.select V hV) where
  basis := b
  relation := C.selectedRelation V
  relation_span := C.selectedRelation_span V hV

def selectedEquivalence (b : Module.Basis τ ℂ V) :
    (P.select V hV).Coefficient ≃ₗ[ℂ] (C.selectedPresentation V hV b).rows :=
  (C.selectedPresentation V hV b).equivalence

theorem selected_prescribed_iff (b : Module.Basis τ ℂ V) (c : τ → ℂ) :
    (∃ f : (P.select V hV).Coefficient, ∀ i, f.val (b i) = c i) ↔
      c ∈ (C.selectedPresentation V hV b).rows :=
  (C.selectedPresentation V hV b).prescribed_iff c

/-- A basis can also be chosen internally; this route is noncomputable. -/
def canonicalSelectedPresentation := C.selectedPresentation V hV (Module.Basis.ofVectorSpace ℂ V)

def canonicalSelectedEquivalence : (P.select V hV).Coefficient ≃ₗ[ℂ]
    (C.canonicalSelectedPresentation V hV).rows :=
  (C.canonicalSelectedPresentation V hV).equivalence

end
end Math.AllOrderDerivativeCoordinates.Presentation
