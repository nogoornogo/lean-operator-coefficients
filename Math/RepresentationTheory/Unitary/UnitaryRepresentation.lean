import Math.RepresentationTheory.Multiplicity.UnitaryMultiplicity

/-! # Unitary representation compatibility interface

Declaration namespaces are retained from the original application module.
-/

namespace Math.CompactEmbeddingClassification
noncomputable section

section UnitaryCompleteReducibility

variable {G E : Type*} [Group G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

abbrev IsUnitaryRepresentation (ρ : Representation ℂ G E) : Prop :=
  UnitaryMultiplicity.IsUnitaryRepresentation ρ

/-- The orthogonal complement of an invariant subspace is invariant under a
unitary group representation. -/
abbrev orthogonalSubrepresentation
    (ρ : Representation ℂ G E) (hρ : IsUnitaryRepresentation ρ)
    (S : Subrepresentation ρ) : Subrepresentation ρ :=
  UnitaryMultiplicity.orthogonalSubrepresentation ρ hρ S

theorem isCompl_orthogonalSubrepresentation
    (ρ : Representation ℂ G E) (hρ : IsUnitaryRepresentation ρ)
    (S : Subrepresentation ρ) :
    IsCompl S (orthogonalSubrepresentation ρ hρ S) :=
  UnitaryMultiplicity.isCompl_orthogonalSubrepresentation ρ hρ S

/-- Every finite-dimensional unitary complex representation is semisimple. -/
theorem isSemisimpleRepresentation_of_unitary
    (ρ : Representation ℂ G E) (hρ : IsUnitaryRepresentation ρ) :
    Representation.IsSemisimpleRepresentation ρ :=
  UnitaryMultiplicity.isSemisimpleRepresentation_of_unitary ρ hρ

end UnitaryCompleteReducibility

end
end Math.CompactEmbeddingClassification
