import Math.Audit.ImportOrigin
import Physics.FieldTheory.Mass.SelfDualMassIndex
import Physics.FieldTheory.Mass.Audit.AuditAbelianMassSpectrum
import Mathlib.GroupTheory.Perm.Fin

open Math

/-! Persistent DUAL-1 controls, independent of the choice of GUT group. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU5).isPrefixOf mod || (`GUT.SU6).isPrefixOf mod then
      throwError "Self-dual mass index imports a gauge-specific module: {mod}"

namespace GUT.AuditSelfDualMassIndex

noncomputable section

open InvariantWeylMass AuditAbelianMassSpectrum

theorem signMass_nondegenerate : signMass.form.Nondegenerate := by
  constructor
  · intro x hx
    simpa [signMass] using hx 1
  · intro x hx
    simpa [signMass] using hx 1

def signSelfDual : Representation.Equiv (scalar signCharacter) (scalar signCharacter).dual :=
  .mk (signMass.form.toDual signMass_nondegenerate) (by
    intro g
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    exact signMass.form_covariant g x)

theorem zero_mass_zero_index (g : ℤˣ) :
    (SymmetricMass.zero (scalar signCharacter)).radical.toRepresentation.character g -
      (SymmetricMass.zero (scalar signCharacter)).radical.toRepresentation.dual.character g = 0 :=
  SymmetricMass.radical_dual_character_zero_of_equiv _ signSelfDual g

/-- Zero dual index does not force all modes to be massive. -/
theorem zero_mass_retains_modes :
    (SymmetricMass.zero (scalar signCharacter)).radical.toSubmodule ≠ ⊥ := by
  rw [SymmetricMass.radical_zero]
  exact top_ne_bot

theorem nonzero_mass_zero_index : signMass.form ≠ 0 ∧
    ∀ g, signMass.radical.toRepresentation.character g -
      signMass.radical.toRepresentation.dual.character g = 0 :=
  ⟨signMass_nonzero, signMass.radical_dual_character_zero_of_equiv signSelfDual⟩

/-- The pointwise hypothesis works for a non-Abelian ambient group. -/
theorem perm3_inverse_conjugate : ∀ g : Equiv.Perm (Fin 3),
    ∃ n, g⁻¹ = n * g * n⁻¹ := by decide

theorem perm3_mass_zero_index {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (rho : Representation ℂ (Equiv.Perm (Fin 3)) V)
    (B : SymmetricMass rho) (g : Equiv.Perm (Fin 3)) :
    B.radical.toRepresentation.character g -
      B.radical.toRepresentation.dual.character g = 0 := by
  exact SymmetricMass.restricted_radical_dual_character_zero_of_conjugate_inverse
    rho (MonoidHom.id _) B perm3_inverse_conjugate g

/-- A genuine U(1) charge has nonzero light index at zero mass. -/
theorem circle_zero_mass_nonzero_index :
    (SymmetricMass.zero (scalar (MonoidHom.id Circle))).radical.toRepresentation.character
        imaginaryUnit -
      (SymmetricMass.zero (scalar (MonoidHom.id Circle))).radical.toRepresentation.dual.character
        imaginaryUnit ≠ 0 := by
  rw [SymmetricMass.radical_dual_character_eq, Representation.char_dual,
    scalar_character, scalar_character]
  change Complex.I - (imaginaryUnit⁻¹ : Circle) ≠ 0
  rw [Circle.coe_inv]
  change Complex.I - Complex.I⁻¹ ≠ 0
  norm_num [Complex.ext_iff]

#print axioms SelfDualCharacter.character_eq_inv_of_equiv
#print axioms SelfDualCharacter.restrict_character_eq_dual_of_equiv
#print axioms SelfDualCharacter.restrict_character_eq_dual_of_conjugate_inverse
#print axioms SelfDualCharacter.restrict_character_eq_dual_of_inversion_element
#print axioms SelfDualCharacter.virtualCharacter_restrict_inv
#print axioms SymmetricMass.radical_dual_character_zero_at
#print axioms SymmetricMass.radical_dual_character_zero_of_equiv
#print axioms SymmetricMass.restricted_radical_dual_character_zero_of_equiv
#print axioms SymmetricMass.restricted_radical_dual_character_zero_of_conjugate_inverse
#print axioms SymmetricMass.restricted_radical_dual_character_zero_of_inversion_element
#print axioms signSelfDual
#print axioms zero_mass_zero_index
#print axioms zero_mass_retains_modes
#print axioms nonzero_mass_zero_index
#print axioms perm3_mass_zero_index
#print axioms circle_zero_mass_nonzero_index

end

end GUT.AuditSelfDualMassIndex
