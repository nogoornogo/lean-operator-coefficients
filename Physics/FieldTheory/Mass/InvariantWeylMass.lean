import Physics.FieldTheory.Mass.DiracWeylConvention
import Physics.FieldTheory.Mass.SymmetricMassIndex

open Math

/-!
# Invariant symmetric Weyl mass coefficients

The radical is the exact zero-mode representation. The quotient carries a
nondegenerate invariant symmetric form and is therefore self-dual. For a
finite-dimensional action this conserves the dual chiral character,
not a chosen signed Dirac index. No mass-rank or amplitude assumption is made.
-/

set_option autoImplicit false

namespace GUT.InvariantWeylMass

noncomputable section

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]

section Unitary

open CompactEmbeddingClassification EquivariantMassIndex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {sigma : Representation ℂ G E}

set_option linter.unusedVariables false in
/-- Removing the entire massive quotient preserves precisely the dual
chiral character. Compatibility wrapper for the older unitary interface. -/
theorem radical_dual_character_eq (B : SymmetricMass sigma)
    (h : IsUnitaryRepresentation sigma) (g : G) :
    B.radical.toRepresentation.character g -
        B.radical.toRepresentation.dual.character g =
      sigma.character g - sigma.dual.character g := by
  exact B.radical_dual_character_eq g

end Unitary

section Dirac

variable {W : Type*} [AddCommGroup W] [Module ℂ W]
  {rhoV : Representation ℂ G V} {rhoW : Representation ℂ G W}

/-- Existing Dirac sectors embed into this model without changing their
all-left-handed representation or zero-mode subspace. -/
def ofDirac (M : Representation.IntertwiningMap rhoV rhoW) :
    SymmetricMass (rhoV.prod rhoW.dual) where
  form := DiracWeylConvention.massBilinear M
  symmetric := DiracWeylConvention.massBilinear_isSymm M.toLinearMap
  invariant := DiracWeylConvention.massBilinear_invariant M

theorem ofDirac_radical (M : Representation.IntertwiningMap rhoV rhoW) :
    (ofDirac M).radical = DiracWeylConvention.radicalSubrepresentation M := by
  apply Subrepresentation.toSubmodule_injective
  rfl

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

/-- The dual index is the antisymmetrization of the signed index, not that
signed index itself. This identity holds irrespective of the mass map. -/
theorem ofDirac_dual_character_eq_signed_antisymmetrization (g : G) :
    (rhoV.prod rhoW.dual).character g -
        (rhoV.prod rhoW.dual).dual.character g =
      (rhoV.character g - rhoW.character g) -
        (rhoV.character g⁻¹ - rhoW.character g⁻¹) :=
  DiracWeylConvention.allLeft_dual_character_eq_signed_antisymmetrization g

end Dirac

section DiracLightIndex

open CompactEmbeddingClassification EquivariantMassIndex

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {sigmaE : Representation ℂ G E} {sigmaF : Representation ℂ G F}

/-- Specialization to Dirac masses recovers the previous light-index bridge
exactly, with the antisymmetrization kept explicit. -/
theorem ofDirac_radical_dual_character_eq_lightIndex_antisymmetrization
    (M : Representation.IntertwiningMap sigmaE sigmaF)
    (hF : IsUnitaryRepresentation sigmaF) (g : G) :
    (ofDirac M).radical.toRepresentation.character g -
        (ofDirac M).radical.toRepresentation.dual.character g =
      lightIndexCharacter M hF g - lightIndexCharacter M hF g⁻¹ := by
  rw [ofDirac_radical]
  exact DiracWeylConvention.radical_dual_character_eq_lightIndex_antisymmetrization M hF g

end DiracLightIndex

section VirtualCharacterInterface

open PhysicalRestrictionBridge EquivariantMassIndex CompactEmbeddingClassification

variable {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]

/-- The dual chiral difference in the existing finite virtual-character
interface. It is deliberately distinct from `EquivariantMassIndex.lightIndex`. -/
def dualIndex (tau : Representation ℂ G X) : FiniteVirtualGroupRepresentation G :=
  [ { coeff := 1, rep := toActualGroupRepresentation tau },
    { coeff := -1, rep := toActualGroupRepresentation tau.dual } ]

@[simp]
theorem dualIndex_character (tau : Representation ℂ G X) (g : G) :
    FiniteVirtualGroupRepresentation.character (dualIndex tau) g =
      tau.character g - tau.dual.character g := by
  simp [dualIndex, FiniteVirtualGroupRepresentation.character,
    VirtualGroupSummand.character, ActualGroupRepresentation.character,
    toActualGroupRepresentation, sub_eq_add_neg]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {sigma : Representation ℂ G E}

/-- Canonical light dual index, using the actual radical of the mass form. -/
def lightDualIndex (B : SymmetricMass sigma) : FiniteVirtualGroupRepresentation G :=
  dualIndex B.radical.toRepresentation

theorem lightDualIndex_characterEquivalent_ultravioletDualIndex
    (B : SymmetricMass sigma) (h : IsUnitaryRepresentation sigma) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightDualIndex B) (dualIndex sigma) := by
  intro g
  simp only [lightDualIndex, dualIndex_character]
  exact radical_dual_character_eq B h g

/-- A separately identified dual light target transports to the ultraviolet
dual source. It does not furnish a signed or full light-spectrum target. -/
theorem ultravioletDualIndex_characterEquivalent_of_lightDualIndex
    (B : SymmetricMass sigma) (h : IsUnitaryRepresentation sigma)
    (target : FiniteVirtualGroupRepresentation G)
    (hLight : FiniteVirtualGroupRepresentation.CharacterEquivalent (lightDualIndex B) target) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent (dualIndex sigma) target := by
  intro g
  exact (lightDualIndex_characterEquivalent_ultravioletDualIndex B h g).symm.trans (hLight g)

end VirtualCharacterInterface

end

end GUT.InvariantWeylMass
