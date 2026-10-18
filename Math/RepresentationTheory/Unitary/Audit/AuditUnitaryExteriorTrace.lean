import Math.Audit.ImportOrigin
import Math.RepresentationTheory.Unitary.UnitaryEigenbasis
import Math.LinearAlgebra.ExteriorEigenbasisTrace
import Math.LinearAlgebra.RankFiveExteriorSum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Generic spectral and exterior-trace controls, isolated from gauge models. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod ||
        (`GUT.SUN).isPrefixOf mod || (`GUT.Spin).isPrefixOf mod || (`GUT.Sp).isPrefixOf mod then
      throwError "Generic spectral audit imports a gauge family: {mod}"

namespace Math.UnitaryEigenbasis.Audit

noncomputable section

abbrev EmptySpace := EuclideanSpace ℂ (Fin 0)

/-- No positive-dimension hypothesis is hidden in the cyclic restriction. -/
theorem empty_eigenbasis (g : Equiv.Perm (Fin 3)) :
    ∃ (b : Module.Basis (Fin 0) ℂ EmptySpace) (w : Fin 0 → Circle),
      ∀ i, Representation.trivial ℂ (Equiv.Perm (Fin 3)) EmptySpace g (b i) =
        (w i : ℂ) • b i := by
  apply exists_element_basis _ (fun _ _ _ => rfl) g 0
  simp [EmptySpace]

theorem repeated_eigenvalue (g : Equiv.Perm (Fin 3)) :
    ∃ (b : Module.Basis (Fin 2) ℂ (EuclideanSpace ℂ (Fin 2))) (w : Fin 2 → Circle),
      (∀ i, Representation.trivial ℂ (Equiv.Perm (Fin 3)) _ g (b i) =
        (w i : ℂ) • b i) ∧ ∀ i, w i = 1 := by
  obtain ⟨b, w, he⟩ := exists_element_basis
    (Representation.trivial ℂ (Equiv.Perm (Fin 3)) (EuclideanSpace ℂ (Fin 2)))
    (fun _ _ _ => rfl) g 2 (by simp)
  refine ⟨b, w, he, ?_⟩
  intro i
  have h : (w i : ℂ) • b i = (1 : ℂ) • b i := by simpa using (he i).symm
  apply Circle.coe_injective
  exact (smul_left_injective ℂ (b.ne_zero i)) h

theorem determinant_hypothesis_needed :
    (∑ s : Set.powersetCard (Fin 5) 4, ∏ _i ∈ s.val, (2 : ℂ)) ≠
      ∑ _i : Fin 5, (2 : ℂ)⁻¹ := by
  simp only [Finset.prod_const, Set.powersetCard.card_eq]
  have hc : Fintype.card (Set.powersetCard (Fin 5) 4) = 5 := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
    norm_num [Nat.choose]
  simp only [Finset.sum_const, Finset.card_univ, hc]
  norm_num

#print axioms exists_character_basis
#print axioms exists_element_basis
#print axioms ExteriorEigenbasisTrace.algebra_eigen
#print axioms RankFiveExteriorSum.by_degree
#print axioms RankFiveExteriorSum.degree_four
#print axioms RankFiveExteriorSum.determinant_one
#print axioms empty_eigenbasis
#print axioms repeated_eigenvalue
#print axioms determinant_hypothesis_needed

end

end Math.UnitaryEigenbasis.Audit
