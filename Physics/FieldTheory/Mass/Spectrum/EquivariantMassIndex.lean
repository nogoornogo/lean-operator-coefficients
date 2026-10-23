import Math.RepresentationTheory.Unitary.UnitarySubrepresentationOrthogonality
import Math.RepresentationTheory.Characters.VirtualRepresentation
import Math.RepresentationTheory.Characters.CharacterExact
import Mathlib.RepresentationTheory.Character

open Math

/-!
# Character index of an equivariant mass map

This module isolates the finite-dimensional linear-algebra statement behind
integrating out vectorlike massive states.  For an equivariant map between
unitary representations, its kernel and the orthogonal complement of its
range carry the unmatched (light) representations.  Their virtual character
is the difference of the original source and target characters.
The algebraic foundation is `CharacterExact`: its quotient cokernel is
identified here with the invariant orthogonal complement in the target.

No assertion is made here that a particular physical Lagrangian supplies the
invariant pairing or the claimed light spectrum.  Those remain separate
physical inputs.
-/

namespace Physics
namespace EquivariantMassIndex

open CompactEmbeddingClassification

noncomputable section

universe u v w

variable {G : Type u} {E : Type v} [Group G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- A unitary representation is the product of an invariant subrepresentation
and its invariant orthogonal complement. -/
def orthogonalDecompositionEquiv
    (rho : Representation ℂ G E) (hUnitary : IsUnitaryRepresentation rho)
    (S : Subrepresentation rho) :
    Representation.Equiv
      (S.toRepresentation.prod
        (orthogonalSubrepresentation rho hUnitary S).toRepresentation)
      rho := by
  let T := orthogonalSubrepresentation rho hUnitary S
  have hCompl : IsCompl S.toSubmodule T.toSubmodule := by
    change IsCompl S.toSubmodule S.toSubmoduleᗮ
    exact S.toSubmodule.isCompl_orthogonal
  apply Representation.Equiv.mk (S.toSubmodule.prodEquivOfIsCompl T.toSubmodule hCompl)
  intro g
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change rho g x + rho g y = rho g (x + y)
  exact ((rho g).map_add x y).symm

/-- The invariant orthogonal complement realizes the algebraic quotient. -/
def orthogonalQuotientEquiv
    (rho : Representation ℂ G E) (hUnitary : IsUnitaryRepresentation rho)
    (S : Subrepresentation rho) :
    Representation.Equiv
      (orthogonalSubrepresentation rho hUnitary S).toRepresentation
      (CharacterExact.quotientRepresentation S) :=
  CharacterExact.complementQuotientEquiv S (orthogonalSubrepresentation rho hUnitary S)
    S.toSubmodule.isCompl_orthogonal

/-- The character of a finite-dimensional unitary representation splits as
the sum of the characters on an invariant subspace and its orthogonal
complement. -/
theorem character_eq_add_orthogonal
    (rho : Representation ℂ G E) (hUnitary : IsUnitaryRepresentation rho)
    (S : Subrepresentation rho) (g : G) :
    rho.character g =
      S.toRepresentation.character g +
        (orthogonalSubrepresentation rho hUnitary S).toRepresentation.character g := by
  rw [CharacterExact.character_eq_sub_add_quotient S g]
  rw [congrFun (Representation.char_iso (orthogonalQuotientEquiv rho hUnitary S)) g]

variable {V : Type v} {W : Type w}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {rhoV : Representation ℂ G V}
variable {rhoW : Representation ℂ G W}

/-!
## From an invariant mass pairing to an intertwiner

The representation-theoretic mass-index theorem takes an intertwining map as
input.  A Lagrangian usually presents the same condition as invariance of the
Hermitian pairing `inner w (M v)` under simultaneous transformations.  The
following bridge proves these formulations equivalent when the target action
is unitary.
-/

/-- A linear mass map whose associated Hermitian pairing is invariant under
simultaneous source and target transformations. -/
structure InvariantMassPairing
    (rhoV : Representation ℂ G V) (rhoW : Representation ℂ G W) where
  toLinearMap : V →ₗ[ℂ] W
  invariant' : ∀ g v w,
    inner ℂ (rhoW g w) (toLinearMap (rhoV g v)) =
      inner ℂ w (toLinearMap v)

namespace InvariantMassPairing

/-- Invariance of the Hermitian mass pairing implies equivariance of the
underlying mass map. -/
theorem intertwines
    (M : InvariantMassPairing rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) (g : G) (v : V) :
    M.toLinearMap (rhoV g v) = rhoW g (M.toLinearMap v) := by
  apply ext_inner_left ℂ
  intro y
  calc
    inner ℂ y (M.toLinearMap (rhoV g v)) =
        inner ℂ (rhoW g (rhoW g⁻¹ y))
          (M.toLinearMap (rhoV g v)) := by simp
    _ = inner ℂ (rhoW g⁻¹ y) (M.toLinearMap v) :=
      M.invariant' g v (rhoW g⁻¹ y)
    _ = inner ℂ (rhoW g (rhoW g⁻¹ y))
          (rhoW g (M.toLinearMap v)) :=
      (hW g (rhoW g⁻¹ y) (M.toLinearMap v)).symm
    _ = inner ℂ y (rhoW g (M.toLinearMap v)) := by simp

/-- Convert a physically stated invariant mass pairing into the exact
intertwiner interface used by the mass-index theorem. -/
def toIntertwiningMap
    (M : InvariantMassPairing rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) :
    Representation.IntertwiningMap rhoV rhoW where
  toLinearMap := M.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    exact M.intertwines hW g

/-- Every intertwiner defines an invariant Hermitian mass pairing when the
target representation is unitary. -/
def ofIntertwiningMap
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) :
    InvariantMassPairing rhoV rhoW where
  toLinearMap := f
  invariant' g v w := by
    change inner ℂ (rhoW g w) (f (rhoV g v)) = inner ℂ w (f v)
    calc
      inner ℂ (rhoW g w) (f (rhoV g v)) =
          inner ℂ (rhoW g w) (rhoW g (f v)) :=
        congrArg (fun x => inner ℂ (rhoW g w) x)
          (Representation.IntertwiningMap.isIntertwining rhoV rhoW f g v)
      _ = inner ℂ w (f v) := hW g w (f v)

@[simp]
theorem toIntertwiningMap_toLinearMap
    (M : InvariantMassPairing rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) :
    (M.toIntertwiningMap hW : V →ₗ[ℂ] W) = M.toLinearMap :=
  rfl

@[simp]
theorem ofIntertwiningMap_toIntertwiningMap
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) :
    (ofIntertwiningMap f hW).toIntertwiningMap hW = f := by
  ext v
  rfl

end InvariantMassPairing

variable [FiniteDimensional ℂ V]
variable [FiniteDimensional ℂ W]

/-- The restriction of an intertwiner from the orthogonal complement of its
kernel to its invariant range. -/
def kernelComplementToRange
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hV : IsUnitaryRepresentation rhoV) :
    Representation.IntertwiningMap
      (orthogonalSubrepresentation rhoV hV f.ker).toRepresentation
      f.range.toRepresentation where
  toLinearMap := {
    toFun := fun x => ⟨f x, ⟨x, rfl⟩⟩
    map_add' := by intro x y; ext; exact f.map_add x y
    map_smul' := by intro c x; ext; exact f.map_smul c x }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining rhoV rhoW f g x

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
@[simp]
theorem kernelComplementToRange_apply
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hV : IsUnitaryRepresentation rhoV)
    (x : (orthogonalSubrepresentation rhoV hV f.ker).toSubmodule) :
    (kernelComplementToRange f hV x : W) = f x :=
  rfl

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- The kernel-complement restriction of an intertwiner is injective. -/
theorem kernelComplementToRange_injective
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hV : IsUnitaryRepresentation rhoV) :
    Function.Injective (kernelComplementToRange f hV) := by
  intro x y hxy
  apply Subtype.ext
  have hKernel : (x : V) - y ∈ f.ker.toSubmodule := by
    change f ((x : V) - y) = 0
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val hxy
  have hOrthogonal : (x : V) - y ∈
      (orthogonalSubrepresentation rhoV hV f.ker).toSubmodule :=
    Submodule.sub_mem _ x.property y.property
  have hZero : (x : V) - y = 0 := by
    change (x : V) - y ∈ f.ker.toSubmoduleᗮ at hOrthogonal
    have hBot : (x : V) - y ∈ (⊥ : Submodule ℂ V) := by
      rw [← Submodule.inf_orthogonal_eq_bot f.ker.toSubmodule]
      exact ⟨hKernel, hOrthogonal⟩
    exact hBot
  exact sub_eq_zero.mp hZero

omit [FiniteDimensional ℂ W] in
/-- The kernel-complement restriction of an intertwiner is surjective onto
its range. -/
theorem kernelComplementToRange_surjective
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hV : IsUnitaryRepresentation rhoV) :
    Function.Surjective (kernelComplementToRange f hV) := by
  rintro ⟨y, x, hxy⟩
  let z : V := x - f.ker.toSubmodule.starProjection x
  have hz : z ∈ (orthogonalSubrepresentation rhoV hV f.ker).toSubmodule :=
    f.ker.toSubmodule.sub_starProjection_mem_orthogonal x
  refine ⟨⟨z, hz⟩, ?_⟩
  apply Subtype.ext
  change f z = y
  rw [show z = x - f.ker.toSubmodule.starProjection x by rfl, map_sub]
  have hProjectionKernel :
      f (f.ker.toSubmodule.starProjection x) = 0 :=
    f.ker.toSubmodule.starProjection_apply_mem x
  rw [hProjectionKernel, sub_zero]
  exact hxy

/-- The non-kernel part of the source is representation-isomorphic to the
range of an equivariant map. -/
def kernelComplementRangeEquiv
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hV : IsUnitaryRepresentation rhoV) :
    Representation.Equiv
      (orthogonalSubrepresentation rhoV hV f.ker).toRepresentation
      f.range.toRepresentation :=
  Representation.IntertwiningMap.ofBijective
    (kernelComplementToRange f hV)
    ⟨kernelComplementToRange_injective f hV,
      kernelComplementToRange_surjective f hV⟩

/-- The light virtual character of an equivariant mass map: unmatched source
modes minus unmatched target modes. -/
def lightIndexCharacter
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) (g : G) : ℂ :=
  f.ker.toRepresentation.character g -
    (orthogonalSubrepresentation rhoW hW f.range).toRepresentation.character g

omit [FiniteDimensional ℂ V] in
/-- The old orthogonal light index equals the algebraic kernel/cokernel
index on the same intertwiner. Only target unitarity is used. -/
theorem lightIndexCharacter_eq_indexCharacter
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) (g : G) :
    lightIndexCharacter f hW g = CharacterExact.indexCharacter f g := by
  unfold lightIndexCharacter CharacterExact.indexCharacter CharacterExact.cokernelRepresentation
  rw [congrFun (Representation.char_iso (orthogonalQuotientEquiv rhoW hW f.range)) g]

/-- Source unitarity is unnecessary even for the orthogonal realization. -/
theorem lightIndexCharacter_eq_source_sub_target_of_target_unitary
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW) (g : G) :
    lightIndexCharacter f hW g = rhoV.character g - rhoW.character g := by
  rw [lightIndexCharacter_eq_indexCharacter]
  exact CharacterExact.indexCharacter_eq_source_sub_target f g

set_option linter.unusedVariables false in
/-- Integrating out the paired range does not change the virtual character.
Compatibility wrapper retaining the older source-unitarity argument. -/
theorem lightIndexCharacter_eq_source_sub_target
    (f : Representation.IntertwiningMap rhoV rhoW)
    (hV : IsUnitaryRepresentation rhoV)
    (hW : IsUnitaryRepresentation rhoW) (g : G) :
    lightIndexCharacter f hW g = rhoV.character g - rhoW.character g := by
  exact lightIndexCharacter_eq_source_sub_target_of_target_unitary f hW g

/-!
## Packaging as finite virtual representations

The project's standard charge-orbit bridge target comparison is expressed with finite lists of actual
group representations.  The following definitions expose the mass-index
identity in exactly that interface.
-/

open PhysicalRestrictionBridge

variable {V₀ W₀ : Type}
variable [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀]
variable [FiniteDimensional ℂ V₀]
variable [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
variable [FiniteDimensional ℂ W₀]
variable {rhoV₀ : Representation ℂ G V₀}
variable {rhoW₀ : Representation ℂ G W₀}

/-- Bundle a finite-dimensional representation in the common physical
virtual-character interface. -/
def toActualGroupRepresentation {X : Type}
    [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    (rho : Representation ℂ G X) : ActualGroupRepresentation G where
  V := X
  rho := rho

/-- The virtual representation carried by unmatched light modes. -/
def lightIndex
    (f : Representation.IntertwiningMap rhoV₀ rhoW₀)
    (hW : IsUnitaryRepresentation rhoW₀) :
    FiniteVirtualGroupRepresentation G :=
  [
    { coeff := 1
      rep := toActualGroupRepresentation f.ker.toRepresentation },
    { coeff := -1
      rep := toActualGroupRepresentation
        (orthogonalSubrepresentation rhoW₀ hW f.range).toRepresentation }
  ]

/-- The ultraviolet source-minus-target virtual representation associated
with the same mass map. -/
def ultravioletIndex :
    FiniteVirtualGroupRepresentation G :=
  [
    { coeff := 1
      rep := toActualGroupRepresentation rhoV₀ },
    { coeff := -1
      rep := toActualGroupRepresentation rhoW₀ }
  ]

@[simp]
theorem lightIndex_character
    (f : Representation.IntertwiningMap rhoV₀ rhoW₀)
    (hW : IsUnitaryRepresentation rhoW₀) (g : G) :
    FiniteVirtualGroupRepresentation.character (lightIndex f hW) g =
      lightIndexCharacter f hW g := by
  simp [lightIndex, lightIndexCharacter,
    FiniteVirtualGroupRepresentation.character,
    PhysicalRestrictionBridge.VirtualGroupSummand.character,
    PhysicalRestrictionBridge.ActualGroupRepresentation.character,
    toActualGroupRepresentation, sub_eq_add_neg]

@[simp]
theorem ultravioletIndex_character (g : G) :
    FiniteVirtualGroupRepresentation.character
        (ultravioletIndex (rhoV₀ := rhoV₀) (rhoW₀ := rhoW₀)) g =
      rhoV₀.character g - rhoW₀.character g := by
  simp [ultravioletIndex, FiniteVirtualGroupRepresentation.character,
    PhysicalRestrictionBridge.VirtualGroupSummand.character,
    PhysicalRestrictionBridge.ActualGroupRepresentation.character,
    toActualGroupRepresentation, sub_eq_add_neg]

/-- The unmatched light modes and the ultraviolet source-minus-target pair
define the same virtual character. -/
theorem lightIndex_characterEquivalent_ultravioletIndex
    (f : Representation.IntertwiningMap rhoV₀ rhoW₀)
    (hV : IsUnitaryRepresentation rhoV₀)
    (hW : IsUnitaryRepresentation rhoW₀) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightIndex f hW)
      (ultravioletIndex (rhoV₀ := rhoV₀) (rhoW₀ := rhoW₀)) := by
  intro g
  rw [lightIndex_character, ultravioletIndex_character]
  exact lightIndexCharacter_eq_source_sub_target f hV hW g

/-- Therefore an independently identified light target is also the virtual
character of the ultraviolet source-minus-target pair. -/
theorem ultravioletIndex_characterEquivalent_of_lightIndex
    (f : Representation.IntertwiningMap rhoV₀ rhoW₀)
    (hV : IsUnitaryRepresentation rhoV₀)
    (hW : IsUnitaryRepresentation rhoW₀)
    (target : FiniteVirtualGroupRepresentation G)
    (hLight : FiniteVirtualGroupRepresentation.CharacterEquivalent
      (lightIndex f hW) target) :
    FiniteVirtualGroupRepresentation.CharacterEquivalent
      (ultravioletIndex (rhoV₀ := rhoV₀) (rhoW₀ := rhoW₀))
      target := by
  intro g
  exact
    (lightIndex_characterEquivalent_ultravioletIndex f hV hW g).symm.trans
      (hLight g)

end

end EquivariantMassIndex
end Physics
