import Math.Audit.ImportOrigin
import GUT.Sp.RestrictedCharacter
import GUT.Sp.Audit.AuditTorus
import Math.LieGroups.Symplectic.Audit.AuditEigenvectorPair

open Math

/-! SP-2 arbitrary-element conjugacy, including elements outside the
chosen torus. The single SP-1 conjugator must not be used for all elements. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Symplectic all-element conjugacy imports a gauge-specific module: {mod}"

namespace GUT.CompactSymplectic.AuditTorusConjugacy

open Math.CompactSymplectic
noncomputable section

theorem inversionElement_outside_torus :
    ¬ ∃ z : Torus 1, torusHom 1 z = inversionElement 1 := by
  rintro ⟨z, hz⟩
  have hh := congrArg (fun g : Group 1 => matrix g (.inl 0) (.inr 0)) hz
  norm_num [torusMatrix, Matrix.J] at hh

theorem off_torus_inverse_conjugate :
    ∃ u : Group 1, (inversionElement 1)⁻¹ = u * inversionElement 1 * u⁻¹ :=
  inverse_conjugate _

theorem fixed_J_not_universal :
    (inversionElement 1)⁻¹ ≠
      inversionElement 1 * inversionElement 1 * (inversionElement 1)⁻¹ := by
  rw [mul_inv_cancel_right]
  intro he
  apply AuditTorus.rank_one_not_involution
  simpa only [pow_two, he] using inv_mul_cancel (inversionElement 1)

theorem full_group_zero_mass_index (n : ℕ) (g : Group n) :
    (InvariantWeylMass.SymmetricMass.zero (defining n)).radical.toRepresentation.character g -
      (InvariantWeylMass.SymmetricMass.zero (defining n)).radical.toRepresentation.dual.character g =
        0 := restricted_mass_zero_index (defining n) (MonoidHom.id _) _ g

#print axioms hilbertData
#print axioms exists_paired_eigenbasis
#print axioms basisMatrix_unitary
#print axioms basisMatrix_symplectic
#print axioms exists_torus_conjugate
#print axioms inverse_conjugate
#print axioms restriction_inverse_conjugate
#print axioms restricted_character_eq_dual
#print axioms restricted_mass_zero_index
#print axioms virtualCharacter_inv
#print axioms inversionElement_outside_torus
#print axioms off_torus_inverse_conjugate
#print axioms fixed_J_not_universal
#print axioms full_group_zero_mass_index

end

end GUT.CompactSymplectic.AuditTorusConjugacy
