import Math.Audit.ImportOrigin
import GUT.Sp.TorusCharacters
import Math.LieGroups.Symplectic.UnitaryEmbedding
import Math.LieGroups.Symplectic.QuaternionicStructure

open Physics

open Math

/-! SP-1: actual compact carrier, torus inversion, and boundary controls.
The matrix J has order four at positive rank, not order two. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Symplectic torus core imports a gauge-specific module: {mod}"

namespace GUT.CompactSymplectic.AuditTorus

open Math.CompactSymplectic
noncomputable section

example (n : ℕ) : CompactSpace (Group n) := inferInstance
example (n : ℕ) : IsTopologicalGroup (Group n) := inferInstance

theorem rank_zero (g : Group 0) : g = 1 := by
  apply matrix_injective 0
  ext i j
  exact isEmptyElim i

theorem inversion_square (n : ℕ) : matrix (inversionElement n ^ 2) = -1 := by
  simp only [pow_two, matrix_mul, matrix_inversionElement, Matrix.J_squared]

theorem inversion_fourth (n : ℕ) : inversionElement n ^ 4 = 1 := by
  apply matrix_injective n
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, matrix_mul,
    inversion_square, matrix_one]
  simp

theorem rank_one_not_involution : inversionElement 1 ^ 2 ≠ 1 := by
  intro he
  have hm := congrArg (matrix (n := 1)) he
  rw [inversion_square, matrix_one] at hm
  have hh := congrArg (fun A : Mat 1 => A (.inl 0) (.inl 0)) hm
  norm_num at hh

def imaginaryUnit : Circle := ⟨Complex.I, mem_sphere_zero_iff_norm.mpr (by simp)⟩

theorem torus_not_fixed_by_inversion :
    torusHom 1 (fun _ => imaginaryUnit) ≠ (torusHom 1 (fun _ => imaginaryUnit))⁻¹ := by
  intro he
  rw [← map_inv] at he
  have hh := congrArg (fun z : Torus 1 => (z 0 : ℂ)) (torusHom_injective 1 he)
  change Complex.I = (imaginaryUnit⁻¹ : Circle) at hh
  rw [Circle.coe_inv] at hh
  change Complex.I = Complex.I⁻¹ at hh
  norm_num [Complex.ext_iff] at hh

abbrev defining := Math.CompactSymplectic.defining

def torusDefining (n : ℕ) : Representation ℂ (Torus n) (Index n → ℂ) :=
  (defining n).comp (torusHom n)

theorem defining_zero_mass_zero_index (n : ℕ) (z : Torus n) :
    (InvariantWeylMass.SymmetricMass.zero (torusDefining n)).radical.toRepresentation.character z -
      (InvariantWeylMass.SymmetricMass.zero (torusDefining n)).radical.toRepresentation.dual.character z =
        0 := torus_mass_zero_index (defining n) _ z

theorem rank_one_zero_mass_retains_modes :
    (InvariantWeylMass.SymmetricMass.zero (torusDefining 1)).radical.toSubmodule ≠ ⊥ := by
  rw [InvariantWeylMass.SymmetricMass.radical_zero]
  exact top_ne_bot

#print axioms subgroup_isClosed
#print axioms matrix_det
#print axioms toSpecialUnitary_injective
#print axioms toSpecialUnitary_continuous
#print axioms torusMatrix_unitary
#print axioms torusMatrix_symplectic
#print axioms torusHom
#print axioms torusHom_injective
#print axioms torusHom_continuous
#print axioms inversionElement
#print axioms torusHom_inverse_conjugate
#print axioms unitaryInclusion
#print axioms unitaryInclusion_injective
#print axioms unitaryInclusion_continuous
#print axioms specialUnitaryInclusion_diagonal
#print axioms torus_character_eq_dual
#print axioms torus_mass_zero_index
#print axioms torus_virtualCharacter_inv
#print axioms rank_zero
#print axioms inversion_square
#print axioms inversion_fourth
#print axioms rank_one_not_involution
#print axioms torus_not_fixed_by_inversion
#print axioms defining_zero_mass_zero_index
#print axioms rank_one_zero_mass_retains_modes

end

end GUT.CompactSymplectic.AuditTorus
