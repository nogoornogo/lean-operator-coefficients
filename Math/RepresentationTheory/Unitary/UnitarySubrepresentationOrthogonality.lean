import Math.RepresentationTheory.Decomposition.Schur
import Math.RepresentationTheory.Unitary.UnitaryRepresentation
import Math.RepresentationTheory.Decomposition.ProductFactorization

/-!
# Orthogonality of inequivalent unitary constituents

For a finite-dimensional unitary representation, orthogonal projection onto
an invariant subspace commutes with the group action.  Consequently, the
projection between irreducible invariant subspaces of different dimensions
vanishes by Schur's lemma, so those subspaces are orthogonal.
-/

namespace Math
namespace UnitarySubrepresentationOrthogonality

open CompactEmbeddingClassification

noncomputable section

universe u

variable {G E : Type u} [Group G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- Orthogonal projection onto an invariant subspace commutes with every
operator in a unitary representation. -/
theorem starProjection_apply_representation
    (rho : Representation ℂ G E) (hUnitary : IsUnitaryRepresentation rho)
    (S : Subrepresentation rho) (g : G) (x : E) :
    S.toSubmodule.starProjection (rho g x) =
      rho g (S.toSubmodule.starProjection x) := by
  apply S.toSubmodule.eq_starProjection_of_mem_orthogonal'
  · exact S.apply_mem_toSubmodule g
      (S.toSubmodule.starProjection_apply_mem x)
  · exact (orthogonalSubrepresentation rho hUnitary S).apply_mem_toSubmodule g
      (S.toSubmodule.sub_starProjection_mem_orthogonal x)
  · rw [map_sub]
    abel

/-- Orthogonal projection from one invariant subspace to another is an
intertwiner. -/
def orthogonalProjectionIntertwiner
    (rho : Representation ℂ G E) (hUnitary : IsUnitaryRepresentation rho)
    (S T : Subrepresentation rho) :
    Representation.IntertwiningMap T.toRepresentation S.toRepresentation where
  toLinearMap := S.toSubmodule.orthogonalProjectionOnto.toLinearMap.comp
    T.toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact starProjection_apply_representation rho hUnitary S g x

@[simp]
theorem orthogonalProjectionIntertwiner_apply
    (rho : Representation ℂ G E) (hUnitary : IsUnitaryRepresentation rho)
    (S T : Subrepresentation rho) (x : T.toSubmodule) :
    orthogonalProjectionIntertwiner rho hUnitary S T x =
      S.toSubmodule.orthogonalProjectionOnto (x : E) :=
  rfl

/-- Distinct-dimensional irreducible invariant subspaces of a unitary
representation are orthogonal. -/
theorem isOrtho_of_irreducible_of_finrank_ne
    (rho : Representation ℂ G E) (hUnitary : IsUnitaryRepresentation rho)
    (S T : Subrepresentation rho)
    [Representation.IsIrreducible S.toRepresentation]
    [Representation.IsIrreducible T.toRepresentation]
    (hDimension : Module.finrank ℂ S.toSubmodule ≠
      Module.finrank ℂ T.toSubmodule) :
    S.toSubmodule ⟂ T.toSubmodule := by
  have hProjection :
      orthogonalProjectionIntertwiner rho hUnitary S T = 0 :=
    BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne
      hDimension.symm (orthogonalProjectionIntertwiner rho hUnitary S T)
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le]
  intro x hx
  have hApply := congrArg
    (fun f : Representation.IntertwiningMap
        T.toRepresentation S.toRepresentation => f ⟨x, hx⟩)
    hProjection
  apply S.toSubmodule.orthogonalProjectionOnto_eq_zero_iff.mp
  simpa [orthogonalProjectionIntertwiner_apply] using hApply

section IntertwinerRanges

variable {V W : Type u}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]
variable {rhoV : Representation ℂ G V}
variable {rhoW : Representation ℂ G W}

/-- An injective intertwiner identifies its source with its invariant range. -/
def rangeEquiv (f : Representation.IntertwiningMap rhoV rhoW)
    (hf : Function.Injective f) :
    Representation.Equiv rhoV f.range.toRepresentation := by
  let fRange : Representation.IntertwiningMap rhoV f.range.toRepresentation :=
    { toLinearMap := f.toLinearMap.rangeRestrict
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        change f (rhoV g x) = rhoW g (f x)
        exact Representation.IntertwiningMap.isIntertwining
          rhoV rhoW f g x }
  apply Representation.IntertwiningMap.ofBijective fRange
  constructor
  · intro x y h
    apply hf
    exact congrArg Subtype.val h
  · rintro ⟨y, x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

/-- The range of an injective intertwiner out of an irreducible
representation is irreducible. -/
theorem range_isIrreducible (f : Representation.IntertwiningMap rhoV rhoW)
    (hf : Function.Injective f) [Representation.IsIrreducible rhoV] :
    Representation.IsIrreducible f.range.toRepresentation := by
  exact ProductFactorization.isIrreducible_of_equiv (rangeEquiv f hf).symm

/-- The range has the same finite dimension as the source of an injective
intertwiner. -/
theorem finrank_range_eq (f : Representation.IntertwiningMap rhoV rhoW)
    (hf : Function.Injective f) :
    Module.finrank ℂ f.range.toSubmodule = Module.finrank ℂ V :=
  (rangeEquiv f hf).toLinearEquiv.finrank_eq.symm

end IntertwinerRanges

end


end UnitarySubrepresentationOrthogonality
end Math
