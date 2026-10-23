import Math.Algebra.Jets.ScalarJetQuadratic
import Math.RepresentationTheory.Jets.JetEquationComparison
import Math.RepresentationTheory.Jets.DerivativeInterface

/-! Bounded comparisons with 1507.07240v1. The one-species quadratic source
is the actual untruncated jet source. No Hilbert-series theorem is assumed. -/
namespace Math.DerivativeLiteratureScalar
set_option autoImplicit false
noncomputable section
open MvPolynomial ScalarJetQuadratic Representation

def freeSymbol : JetDirections.Symbols Unit := (X ())^2

def offInput : DerivativeInterface.Input Unit Source where
  action := trivial ℂ Unit Source
  relations := ScalarJetIBP.relations Unit Unit 2 1
  stable _ _ h := h

def onInput : DerivativeInterface.Input Unit Source where
  action := trivial ℂ Unit Source
  relations := JetEquation.combinedRelations freeSymbol 2 1
  stable _ _ h := h

theorem off_dimension : Module.finrank ℂ offInput.Source = 1 := quotient_finrank

theorem second_eom : second ∈ (JetEquation.gradeProjection freeSymbol 2 2).ker := by
  change JetEquation.gradeProjection freeSymbol 2 2 second = 0
  apply Subtype.ext
  change JetEquation.projection freeSymbol second.val = 0
  have hj : Finsupp.single (jetIndex 2) (1 : ℂ) ∈ JetEquation.relations Unit freeSymbol := by
    have h := JetEquation.descendant_mem (S := Unit) freeSymbol () 1
    change JetDirections.ofSymbols () (1 * (X ())^2) ∈ _ at h
    rw [one_mul, X_pow_eq_monomial, JetDirections.ofSymbols_monomial] at h
    exact h
  have hz : JetEquation.projection freeSymbol (X (jetIndex 2) : Poly) = 0 := by
    rw [JetEquation.projection_X]
    have hq : (JetEquation.relations Unit freeSymbol).mkQ
        (Finsupp.single (jetIndex 2) 1) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hj
    rw [hq, map_zero]
  change JetEquation.projection freeSymbol (monomial secondExponent 1) = 0
  rw [secondExponent, monomial_add_single]
  simp only [← X_pow_eq_monomial, pow_one, map_mul, hz, mul_zero]

theorem on_relations_top : onInput.relations = ⊤ := by
  have hs : second ∈ onInput.relations := Submodule.mem_sup_left second_eom
  have hsum : first + second ∈ onInput.relations :=
    Submodule.mem_sup_right (by
      exact ⟨Finsupp.single () primitive, by
        simpa [JetEquation.offRelations, JetEquation.offDerivatives,
          GradedJetIBP.divergence_single] using derivative_primitive⟩)
  have hf : first ∈ onInput.relations := by
    simpa using onInput.relations.sub_mem hsum hs
  apply top_unique
  intro p _
  rw [source_reconstruct p]
  exact onInput.relations.add_mem (onInput.relations.smul_mem _ hf)
    (onInput.relations.smul_mem _ hs)

theorem on_projection_zero (p : Source) : onInput.projection p = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [on_relations_top]
  trivial

instance : Subsingleton onInput.Source := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := onInput.relations.mkQ_surjective x
  obtain ⟨y, rfl⟩ := onInput.relations.mkQ_surjective y
  exact (on_projection_zero x).trans (on_projection_zero y).symm

theorem on_dimension : Module.finrank ℂ onInput.Source = 0 :=
  Module.finrank_zero_of_subsingleton

theorem on_coefficient_zero (f : onInput.Coefficient) : f = 0 := by
  apply Subtype.ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro p
  have h : p ∈ onInput.relations := by rw [on_relations_top]; trivial
  exact f.property h

theorem off_extraction (f : offInput.Coefficient) :
    offInput.coefficientEquiv f (offInput.projection first) = f.val first := rfl

theorem on_extraction (f : onInput.Coefficient) (p : Source) :
    onInput.coefficientEquiv f (onInput.projection p) = f.val p := rfl

end
end Math.DerivativeLiteratureScalar
