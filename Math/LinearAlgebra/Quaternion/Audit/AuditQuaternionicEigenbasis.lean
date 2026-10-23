import Math.Audit.ImportOrigin
import Math.LinearAlgebra.Quaternion.QuaternionicEigenbasis

/-! The abstract paired spectral theorem has no ambient Math imports. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.Sp).isPrefixOf mod || (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Abstract quaternionic spectral theorem imports a gauge group: {mod}"

namespace Math.QuaternionicSpectral.Audit

noncomputable section

def emptyData : Data (EuclideanSpace ℂ (Fin 0)) where
  q := 0
  square _ := Subsingleton.elim _ _
  pairing v w := by rw [Subsingleton.elim v 0, Subsingleton.elim w 0]; simp
  t := LinearMap.id
  unitary _ _ := rfl
  intertwines _ := rfl

theorem empty_basis : ∃ b : OrthonormalBasis (Fin 0 ⊕ Fin 0) ℂ (EuclideanSpace ℂ (Fin 0)),
    ∀ i, b (.inr i) = emptyData.q (b (.inl i)) := by
  obtain ⟨n, b, z, hq, _⟩ := emptyData.exists_paired_eigenbasis
  have hn : n = 0 := by
    have hh := Module.finrank_eq_card_basis b.toBasis
    simp at hh
    omega
  subst n
  exact ⟨b, hq⟩

theorem no_one_dimensional_quaternionic_data (D : Data ℂ) : False := by
  obtain ⟨n, hn⟩ := D.finrank_eq_twice
  simp only [Module.finrank_self] at hn
  omega

#print axioms Data.q_norm
#print axioms Data.t_norm
#print axioms Data.q_orthogonal
#print axioms Data.restrict
#print axioms Data.exists_unit_eigenvector
#print axioms Frame.paired_orthonormal
#print axioms Frame.q_mem_complement
#print axioms Frame.t_mem_complement
#print axioms Frame.restricted
#print axioms Frame.extend
#print axioms Data.exists_spanning_frame
#print axioms Data.exists_paired_eigenbasis
#print axioms Data.finrank_eq_twice
#print axioms empty_basis
#print axioms no_one_dimensional_quaternionic_data

end

end Math.QuaternionicSpectral.Audit
