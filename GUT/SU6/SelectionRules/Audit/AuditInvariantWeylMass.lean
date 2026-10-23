import Physics.FieldTheory.Mass.Algebra.InvariantWeylMass
import Physics.FieldTheory.Mass.Algebra.WeylMassTwoTorsion

open Physics

/-!
# Audit of the general symmetric mass foundation and its convention boundary

These declarations do not extend E beyond the existing Dirac model class.
Constructor checks and an order-two example prevent treating a conditional
identity or a lossy dual index as an actual light-spectrum classification.
-/

set_option autoImplicit false

open Physics.InvariantWeylMass Physics.WeylMassTwoTorsion

example {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) : SymmetricMass rho := SymmetricMass.zero rho

example : SymmetricMass signRepresentation := majoranaMass

example : Fintype.card ℤˣ = 2 := signGroup_card

example : Module.finrank ℂ (SymmetricMass.zero signRepresentation).radical.toSubmodule = 1 :=
  zero_mass_radical_finrank

example : Module.finrank ℂ majoranaMass.radical.toSubmodule = 0 := majoranaMass_radical_finrank

example {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {rho : Representation ℂ G V} (B : SymmetricMass rho) (g : G) :
    B.radical.toRepresentation.character g - B.radical.toRepresentation.dual.character g =
      rho.character g - rho.dual.character g := B.radical_dual_character_eq g

#print axioms Physics.EquivariantMassIndex.orthogonalQuotientEquiv
#print axioms Physics.EquivariantMassIndex.lightIndexCharacter_eq_indexCharacter
#print axioms Physics.EquivariantMassIndex.lightIndexCharacter_eq_source_sub_target_of_target_unitary
#print axioms SymmetricMass.radical_dual_character_eq
#print axioms SymmetricMass.toIntertwiningMap
#print axioms SymmetricMass.radical
#print axioms SymmetricMass.mem_radical
#print axioms SymmetricMass.quotientRepresentation
#print axioms SymmetricMass.quotientForm
#print axioms SymmetricMass.quotientForm_symmetric
#print axioms SymmetricMass.quotientForm_invariant
#print axioms SymmetricMass.quotientForm_nondegenerate
#print axioms SymmetricMass.complementQuotientEquiv
#print axioms SymmetricMass.quotientSelfDualEquiv
#print axioms SymmetricMass.quotient_character_eq_dual
#print axioms radical_dual_character_eq
#print axioms ofDirac
#print axioms ofDirac_radical
#print axioms ofDirac_dual_character_eq_signed_antisymmetrization
#print axioms ofDirac_radical_dual_character_eq_lightIndex_antisymmetrization
#print axioms dualIndex
#print axioms dualIndex_character
#print axioms lightDualIndex_characterEquivalent_ultravioletDualIndex
#print axioms ultravioletDualIndex_characterEquivalent_of_lightDualIndex
#print axioms signRepresentation_unitary
#print axioms signRepresentation_nontrivial
#print axioms majoranaMass
#print axioms majoranaMass_nondegenerate
#print axioms same_dual_index_different_zero_modes
