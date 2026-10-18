import Math.Audit.ImportOrigin
import Math.LieGroups.Symplectic.EigenvectorPair

/-! SP-2 paired-spectral foundation: actual defining action, repeated
real eigenvalues, and the empty-rank boundary. No torus conjugacy assumed. -/

set_option autoImplicit false
open Matrix

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Symplectic eigenvector foundation imports a gauge-specific module: {mod}"

namespace Math.CompactSymplectic.AuditEigenvectorPair

noncomputable section

def leftVector : Index 1 → ℂ := Pi.single (.inl 0) 1

theorem leftVector_ne_zero : leftVector ≠ 0 := by
  intro he
  have hh := congrFun he (.inl 0)
  norm_num [leftVector] at hh

theorem repeated_positive_eigenvalue :
    defining 1 1 leftVector = leftVector ∧
      defining 1 1 (quaternionicMap 1 leftVector) = quaternionicMap 1 leftVector ∧
      LinearIndependent ℂ ![leftVector, quaternionicMap 1 leftVector] := by
  simp only [map_one, Module.End.one_apply, true_and]
  exact quaternionicMap_pair_independent leftVector_ne_zero

def negativeOne : Circle := ⟨-1, mem_sphere_zero_iff_norm.mpr (by simp)⟩

theorem negative_identity_action (v : Index 1 → ℂ) :
    defining 1 (torusHom 1 (fun _ => negativeOne)) v = -v := by
  have hc : (negativeOne : ℂ) = -1 := rfl
  have hi : ((negativeOne⁻¹ : Circle) : ℂ) = -1 := by
    rw [Circle.coe_inv, hc]
    norm_num
  rw [defining_apply, matrix_torusHom]
  ext i
  cases i <;> simp [torusMatrix, Matrix.mulVec_diagonal, hc, hi]

theorem repeated_negative_eigenvalue :
    defining 1 (torusHom 1 (fun _ => negativeOne)) leftVector = -leftVector ∧
      defining 1 (torusHom 1 (fun _ => negativeOne)) (quaternionicMap 1 leftVector) =
        -quaternionicMap 1 leftVector ∧
      LinearIndependent ℂ ![leftVector, quaternionicMap 1 leftVector] :=
  ⟨negative_identity_action _, negative_identity_action _,
    quaternionicMap_pair_independent leftVector_ne_zero⟩

theorem no_rank_zero_eigenvector : ¬ ∃ v : Index 0 → ℂ, v ≠ 0 := by
  rintro ⟨v, hv⟩
  exact hv (Subsingleton.elim _ _)

#print axioms defining_apply
#print axioms defining_pairing
#print axioms quaternionicMap_matrix
#print axioms quaternionicMap_square
#print axioms matrix_mul_J
#print axioms defining_quaternionic
#print axioms quaternionicMap_ne_zero
#print axioms quaternionicMap_orthogonal
#print axioms quaternionicMap_eigen
#print axioms quaternionicMap_circle_eigen
#print axioms quaternionicMap_pair_independent
#print axioms quaternionicMap_pairing
#print axioms quaternionicMap_preserves_orthogonal_pair
#print axioms defining_eigen_norm
#print axioms exists_eigenvector_pair
#print axioms defining_preserves_orthogonal_pair
#print axioms repeated_positive_eigenvalue
#print axioms repeated_negative_eigenvalue
#print axioms no_rank_zero_eigenvector

end

end Math.CompactSymplectic.AuditEigenvectorPair
