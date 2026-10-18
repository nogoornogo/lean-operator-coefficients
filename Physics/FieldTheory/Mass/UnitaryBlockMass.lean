import Physics.FieldTheory.Mass.UnitaryVirtualRealization

open Math

/-!
# Canonical block mass for unitary representations

An explicit light-plus-heavy decomposition has a canonical equivariant mass
map: it vanishes on the positive light block and identifies the common heavy
block.  Its kernel and orthogonal cokernel are therefore exactly the two
light blocks.  This turns a block decomposition certificate into the
`LightIndexEquiv` consumed by the physical mass-spectrum bridge.
-/

namespace GUT
namespace UnitaryBlockMass

open CompactEmbeddingClassification
open UnitaryVirtualRealization
open UnitaryVirtualRealization.FiniteUnitaryVirtualRepresentation

noncomputable section

universe u

variable {G : Type u} [Group G]

namespace ActualUnitaryGroupRepresentation

/-- First coordinate of the Hilbert direct product. -/
def firstCoordinate
    (R S : ActualUnitaryGroupRepresentation G) (x : (R.product S).V) : R.V :=
  (WithLp.ofLp x).1

/-- Second coordinate of the Hilbert direct product. -/
def secondCoordinate
    (R S : ActualUnitaryGroupRepresentation G) (x : (R.product S).V) : S.V :=
  (WithLp.ofLp x).2

/-- Construct a vector in the Hilbert direct product from its coordinates. -/
def ofCoordinates
    (R S : ActualUnitaryGroupRepresentation G) (x : R.V) (y : S.V) :
    (R.product S).V :=
  WithLp.toLp 2 (x, y)

@[simp]
theorem firstCoordinate_ofCoordinates
    (R S : ActualUnitaryGroupRepresentation G) (x : R.V) (y : S.V) :
    firstCoordinate R S (ofCoordinates R S x y) = x :=
  rfl

@[simp]
theorem secondCoordinate_ofCoordinates
    (R S : ActualUnitaryGroupRepresentation G) (x : R.V) (y : S.V) :
    secondCoordinate R S (ofCoordinates R S x y) = y :=
  rfl

@[simp]
theorem ofCoordinates_zero
    (R S : ActualUnitaryGroupRepresentation G) :
    ofCoordinates R S 0 0 = 0 :=
  rfl

@[simp]
theorem firstCoordinate_zero
    (R S : ActualUnitaryGroupRepresentation G) :
    firstCoordinate R S 0 = 0 :=
  rfl

@[simp]
theorem secondCoordinate_zero
    (R S : ActualUnitaryGroupRepresentation G) :
    secondCoordinate R S 0 = 0 :=
  rfl

/-- Two product vectors agree when both coordinates agree. -/
theorem product_ext
    (R S : ActualUnitaryGroupRepresentation G)
    {x y : (R.product S).V}
    (hFirst : firstCoordinate R S x = firstCoordinate R S y)
    (hSecond : secondCoordinate R S x = secondCoordinate R S y) : x = y := by
  apply WithLp.ofLp_injective
  exact Prod.ext hFirst hSecond

/-- Coordinate formula for the Hermitian product on the Hilbert direct
product. -/
theorem product_inner
    (R S : ActualUnitaryGroupRepresentation G)
    (x y : (R.product S).V) :
    inner ℂ x y =
      inner ℂ (firstCoordinate R S x) (firstCoordinate R S y) +
        inner ℂ (secondCoordinate R S x) (secondCoordinate R S y) :=
  rfl

/-- An equivalence of unitary representations which also preserves the
chosen Hermitian inner products. -/
structure UnitaryEquiv
    (R S : ActualUnitaryGroupRepresentation G) where
  equiv : Representation.Equiv R.rho S.rho
  map_inner : ∀ x y, inner ℂ (equiv x) (equiv y) = inner ℂ x y

namespace UnitaryEquiv

/-- A unitary representation equivalence can be inverted. -/
def symm
    {R S : ActualUnitaryGroupRepresentation G} (e : UnitaryEquiv R S) :
    UnitaryEquiv S R where
  equiv := e.equiv.symm
  map_inner x y := by
    simpa using (e.map_inner (e.equiv.symm x) (e.equiv.symm y)).symm

end UnitaryEquiv

/-- Equivariant projection onto the first coordinate of a Hilbert direct
product. -/
def firstIntertwiner
    (R S : ActualUnitaryGroupRepresentation G) :
    Representation.IntertwiningMap (R.product S).rho R.rho where
  toLinearMap := {
    toFun := firstCoordinate R S
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

/-- The inclusion of an invariant subspace is an intertwining map. -/
def subrepresentationSubtype
    {R : ActualUnitaryGroupRepresentation G} (S : Subrepresentation R.rho) :
    Representation.IntertwiningMap S.toRepresentation R.rho where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

/-- On `L₊ ⊕ P -> L₋ ⊕ P`, kill the light source block and identify the
common paired block `P`. -/
def blockMassMap
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Representation.IntertwiningMap (Lpos.product P).rho (Lneg.product P).rho :=
  (Lneg.productEquiv P).symm.toIntertwiningMap.comp
    ((Representation.IntertwiningMap.inr ℂ Lneg.rho P.rho).comp
      ((Representation.IntertwiningMap.snd ℂ Lpos.rho P.rho).comp
        (Lpos.productEquiv P).toIntertwiningMap))

@[simp]
theorem blockMassMap_apply
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (x : (Lpos.product P).V) :
    blockMassMap Lpos Lneg P x =
      ofCoordinates Lneg P 0 (secondCoordinate Lpos P x) :=
  rfl

@[simp]
theorem blockMassMap_toLinearMap_apply
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (x : (Lpos.product P).V) :
    (blockMassMap Lpos Lneg P).toLinearMap x =
      ofCoordinates Lneg P 0 (secondCoordinate Lpos P x) :=
  blockMassMap_apply Lpos Lneg P x

/-!
## Transport across unitary decompositions
-/

/-- Conjugate the standard block mass by unitary representation
equivalences identifying arbitrary ultraviolet spaces with light-plus-heavy
products. -/
def transportedBlockMassMap
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Representation.IntertwiningMap A.rho B.rho :=
  eB.equiv.symm.toIntertwiningMap.comp
    ((blockMassMap Lpos Lneg P).comp eA.equiv.toIntertwiningMap)

@[simp]
theorem targetEquiv_transportedBlockMassMap_apply
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) (x : A.V) :
    eB.equiv (transportedBlockMassMap A B Lpos Lneg P eA eB x) =
      blockMassMap Lpos Lneg P (eA.equiv x) := by
  simp [transportedBlockMassMap]

/-- Project the kernel of a transported block mass onto its positive light
coordinate. -/
def transportedKernelToPositive
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Representation.IntertwiningMap
      (transportedBlockMassMap A B Lpos Lneg P eA eB).ker.toRepresentation
      Lpos.rho :=
  (firstIntertwiner Lpos P).comp
    (eA.equiv.toIntertwiningMap.comp
      (subrepresentationSubtype
        (R := A) (transportedBlockMassMap A B Lpos Lneg P eA eB).ker))

/-- A kernel vector of a transported block mass has no heavy coordinate in
the chosen source decomposition. -/
theorem second_eq_zero_of_mem_transportedKernel
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P))
    (x : (transportedBlockMassMap A B Lpos Lneg P eA eB).ker.toSubmodule) :
    secondCoordinate Lpos P (eA.equiv x) = 0 := by
  have hx := x.property
  change transportedBlockMassMap A B Lpos Lneg P eA eB x = 0 at hx
  have hMapped := congrArg eB.equiv hx
  have hBlock : blockMassMap Lpos Lneg P (eA.equiv x) = 0 := by
    simpa using hMapped
  have hSecond := congrArg (secondCoordinate Lneg P) hBlock
  simpa [blockMassMap_apply] using hSecond

theorem transportedKernelToPositive_injective
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Function.Injective
      (transportedKernelToPositive A B Lpos Lneg P eA eB) := by
  intro x y hxy
  apply Subtype.ext
  apply eA.equiv.injective
  apply product_ext Lpos P
  · exact hxy
  · exact
      (second_eq_zero_of_mem_transportedKernel A B Lpos Lneg P eA eB x).trans
        (second_eq_zero_of_mem_transportedKernel A B Lpos Lneg P eA eB y).symm

theorem transportedKernelToPositive_surjective
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Function.Surjective
      (transportedKernelToPositive A B Lpos Lneg P eA eB) := by
  intro x
  let y : A.V := eA.equiv.symm (ofCoordinates Lpos P x 0)
  have hy : y ∈
      (transportedBlockMassMap A B Lpos Lneg P eA eB).ker.toSubmodule := by
    change transportedBlockMassMap A B Lpos Lneg P eA eB y = 0
    apply eB.equiv.injective
    calc
      eB.equiv (transportedBlockMassMap A B Lpos Lneg P eA eB y) =
          blockMassMap Lpos Lneg P (eA.equiv y) :=
        targetEquiv_transportedBlockMassMap_apply A B Lpos Lneg P eA eB y
      _ = 0 := by simp [blockMassMap_apply, y]
      _ = eB.equiv 0 := by simp
  refine ⟨⟨y, hy⟩, ?_⟩
  change firstCoordinate Lpos P (eA.equiv y) = x
  simp [y]

/-- The kernel of a transported block mass is representation-isomorphic to
the positive light block. -/
def transportedKernelEquivPositive
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Representation.Equiv
      (transportedBlockMassMap A B Lpos Lneg P eA eB).ker.toRepresentation
      Lpos.rho :=
  Representation.IntertwiningMap.ofBijective
    (transportedKernelToPositive A B Lpos Lneg P eA eB)
    ⟨transportedKernelToPositive_injective A B Lpos Lneg P eA eB,
      transportedKernelToPositive_surjective A B Lpos Lneg P eA eB⟩

/-- Project the orthogonal cokernel of a transported block mass onto its
negative light coordinate. -/
def transportedCokernelToNegative
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Representation.IntertwiningMap
      (orthogonalSubrepresentation B.rho B.unitary
        (transportedBlockMassMap A B Lpos Lneg P eA eB).range).toRepresentation
      Lneg.rho :=
  (firstIntertwiner Lneg P).comp
    (eB.equiv.toIntertwiningMap.comp
      (subrepresentationSubtype
        (R := B) (orthogonalSubrepresentation B.rho B.unitary
          (transportedBlockMassMap A B Lpos Lneg P eA eB).range)))

/-- A vector orthogonal to the transported massive range has no heavy
coordinate in the chosen target decomposition. -/
theorem second_eq_zero_of_mem_transportedCokernel
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P))
    (x : (orthogonalSubrepresentation B.rho B.unitary
      (transportedBlockMassMap A B Lpos Lneg P eA eB).range).toSubmodule) :
    secondCoordinate Lneg P (eB.equiv x) = 0 := by
  have hx := x.property
  change (x : B.V) ∈
    ((transportedBlockMassMap A B Lpos Lneg P eA eB).range.toSubmodule).orthogonal at hx
  rw [Submodule.mem_orthogonal] at hx
  let paired : P.V := secondCoordinate Lneg P (eB.equiv x)
  let sourceWitness : A.V :=
    eA.equiv.symm (ofCoordinates Lpos P 0 paired)
  let rangeVector : B.V :=
    eB.equiv.symm (ofCoordinates Lneg P 0 paired)
  have hRange : rangeVector ∈
      (transportedBlockMassMap A B Lpos Lneg P eA eB).range.toSubmodule := by
    refine ⟨sourceWitness, ?_⟩
    apply eB.equiv.injective
    calc
      eB.equiv
          (transportedBlockMassMap A B Lpos Lneg P eA eB sourceWitness) =
          blockMassMap Lpos Lneg P (eA.equiv sourceWitness) :=
        targetEquiv_transportedBlockMassMap_apply A B Lpos Lneg P eA eB sourceWitness
      _ = ofCoordinates Lneg P 0 paired := by
        simp [sourceWitness, blockMassMap_apply]
      _ = eB.equiv rangeVector := by simp [rangeVector]
  have hInner := hx rangeVector hRange
  have hMappedInner :
      inner ℂ (eB.equiv rangeVector) (eB.equiv x) = 0 :=
    (eB.map_inner rangeVector x).trans hInner
  rw [product_inner] at hMappedInner
  simp [rangeVector, paired] at hMappedInner
  exact hMappedInner

theorem transportedCokernelToNegative_injective
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Function.Injective
      (transportedCokernelToNegative A B Lpos Lneg P eA eB) := by
  intro x y hxy
  apply Subtype.ext
  apply eB.equiv.injective
  apply product_ext Lneg P
  · exact hxy
  · exact
      (second_eq_zero_of_mem_transportedCokernel A B Lpos Lneg P eA eB x).trans
        (second_eq_zero_of_mem_transportedCokernel A B Lpos Lneg P eA eB y).symm

theorem transportedCokernelToNegative_surjective
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Function.Surjective
      (transportedCokernelToNegative A B Lpos Lneg P eA eB) := by
  intro x
  let y : B.V := eB.equiv.symm (ofCoordinates Lneg P x 0)
  have hy : y ∈
      (orthogonalSubrepresentation B.rho B.unitary
        (transportedBlockMassMap A B Lpos Lneg P eA eB).range).toSubmodule := by
    change y ∈
      ((transportedBlockMassMap A B Lpos Lneg P eA eB).range.toSubmodule).orthogonal
    rw [Submodule.mem_orthogonal]
    intro z hz
    rcases hz with ⟨w, rfl⟩
    calc
      inner ℂ (transportedBlockMassMap A B Lpos Lneg P eA eB w) y =
          inner ℂ
            (eB.equiv (transportedBlockMassMap A B Lpos Lneg P eA eB w))
            (eB.equiv y) :=
        (eB.map_inner
          (transportedBlockMassMap A B Lpos Lneg P eA eB w) y).symm
      _ = inner ℂ (blockMassMap Lpos Lneg P (eA.equiv w))
          (ofCoordinates Lneg P x 0) := by
        rw [targetEquiv_transportedBlockMassMap_apply]
        simp [y]
      _ = 0 := by
        rw [product_inner, blockMassMap_apply]
        simp
  refine ⟨⟨y, hy⟩, ?_⟩
  change firstCoordinate Lneg P (eB.equiv y) = x
  simp [y]

/-- The orthogonal cokernel of a transported block mass is
representation-isomorphic to the negative light block. -/
def transportedCokernelEquivNegative
    (A B Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (eA : UnitaryEquiv A (Lpos.product P))
    (eB : UnitaryEquiv B (Lneg.product P)) :
    Representation.Equiv
      (orthogonalSubrepresentation B.rho B.unitary
        (transportedBlockMassMap A B Lpos Lneg P eA eB).range).toRepresentation
      Lneg.rho :=
  Representation.IntertwiningMap.ofBijective
    (transportedCokernelToNegative A B Lpos Lneg P eA eB)
    ⟨transportedCokernelToNegative_injective A B Lpos Lneg P eA eB,
      transportedCokernelToNegative_surjective A B Lpos Lneg P eA eB⟩

/-- Projection from the kernel of the block mass to its positive light
coordinate. -/
def kernelToPositive
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Representation.IntertwiningMap
      (blockMassMap Lpos Lneg P).ker.toRepresentation Lpos.rho where
  toLinearMap := {
    toFun := fun x => firstCoordinate Lpos P x
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

theorem kernelToPositive_injective
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Function.Injective (kernelToPositive Lpos Lneg P) := by
  intro x y hxy
  apply Subtype.ext
  apply product_ext Lpos P
  · exact hxy
  · have hx := x.property
    have hy := y.property
    change blockMassMap Lpos Lneg P x = 0 at hx
    change blockMassMap Lpos Lneg P y = 0 at hy
    have hx' := congrArg (secondCoordinate Lneg P) hx
    have hy' := congrArg (secondCoordinate Lneg P) hy
    have hxZero : secondCoordinate Lpos P x = 0 := by
      simpa [blockMassMap_apply] using hx'
    have hyZero : secondCoordinate Lpos P y = 0 := by
      simpa [blockMassMap_apply] using hy'
    exact hxZero.trans hyZero.symm

theorem kernelToPositive_surjective
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Function.Surjective (kernelToPositive Lpos Lneg P) := by
  intro x
  let y : (Lpos.product P).V := ofCoordinates Lpos P x 0
  have hy : y ∈ (blockMassMap Lpos Lneg P).ker.toSubmodule := by
    change blockMassMap Lpos Lneg P y = 0
    rw [blockMassMap_apply]
    simp [y]
  exact ⟨⟨y, hy⟩, rfl⟩

/-- The kernel of the standard block mass is the positive light block. -/
def kernelEquivPositive
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Representation.Equiv
      (blockMassMap Lpos Lneg P).ker.toRepresentation Lpos.rho :=
  Representation.IntertwiningMap.ofBijective
    (kernelToPositive Lpos Lneg P)
    ⟨kernelToPositive_injective Lpos Lneg P,
      kernelToPositive_surjective Lpos Lneg P⟩

/-- Projection from the orthogonal cokernel of the block mass to its negative
light coordinate. -/
def cokernelToNegative
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Representation.IntertwiningMap
      (orthogonalSubrepresentation (Lneg.product P).rho
        (Lneg.product P).unitary (blockMassMap Lpos Lneg P).range).toRepresentation
      Lneg.rho where
  toLinearMap := {
    toFun := fun x => firstCoordinate Lneg P x
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    rfl

/-- Every vector orthogonal to the range of the standard block mass has zero
paired coordinate. -/
theorem second_eq_zero_of_mem_cokernel
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G)
    (x : (orthogonalSubrepresentation (Lneg.product P).rho
      (Lneg.product P).unitary (blockMassMap Lpos Lneg P).range).toSubmodule) :
    secondCoordinate Lneg P x = 0 := by
  have hx := x.property
  change (x : (Lneg.product P).V) ∈
    ((blockMassMap Lpos Lneg P).range.toSubmodule).orthogonal at hx
  rw [Submodule.mem_orthogonal] at hx
  let z : (Lneg.product P).V :=
    ofCoordinates Lneg P 0 (secondCoordinate Lneg P x)
  have hz : z ∈ (blockMassMap Lpos Lneg P).range.toSubmodule := by
    refine ⟨ofCoordinates Lpos P 0 (secondCoordinate Lneg P x), ?_⟩
    rw [blockMassMap_toLinearMap_apply]
    simp [z]
  have hInner := hx z hz
  rw [product_inner] at hInner
  simp [z] at hInner
  exact hInner

theorem cokernelToNegative_injective
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Function.Injective (cokernelToNegative Lpos Lneg P) := by
  intro x y hxy
  apply Subtype.ext
  apply product_ext Lneg P
  · exact hxy
  · rw [second_eq_zero_of_mem_cokernel Lpos Lneg P x,
      second_eq_zero_of_mem_cokernel Lpos Lneg P y]

theorem cokernelToNegative_surjective
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Function.Surjective (cokernelToNegative Lpos Lneg P) := by
  intro x
  let y : (Lneg.product P).V := ofCoordinates Lneg P x 0
  have hy : y ∈
      (orthogonalSubrepresentation (Lneg.product P).rho
        (Lneg.product P).unitary (blockMassMap Lpos Lneg P).range).toSubmodule := by
    change y ∈ ((blockMassMap Lpos Lneg P).range.toSubmodule).orthogonal
    rw [Submodule.mem_orthogonal]
    intro z hz
    rcases hz with ⟨w, rfl⟩
    rw [product_inner, blockMassMap_toLinearMap_apply]
    simp [y]
  exact ⟨⟨y, hy⟩, rfl⟩

/-- The orthogonal cokernel of the standard block mass is the negative light
block. -/
def cokernelEquivNegative
    (Lpos Lneg P : ActualUnitaryGroupRepresentation G) :
    Representation.Equiv
      (orthogonalSubrepresentation (Lneg.product P).rho
        (Lneg.product P).unitary (blockMassMap Lpos Lneg P).range).toRepresentation
      Lneg.rho :=
  Representation.IntertwiningMap.ofBijective
    (cokernelToNegative Lpos Lneg P)
    ⟨cokernelToNegative_injective Lpos Lneg P,
      cokernelToNegative_surjective Lpos Lneg P⟩

end ActualUnitaryGroupRepresentation

namespace FiniteUnitaryVirtualRepresentation

/-- Any finite unitary virtual target is the light index of its canonical
positive and negative aggregates after adjoining one common massive block. -/
def blockLightIndexEquiv
    (target : FiniteUnitaryVirtualRepresentation G)
    (P : ActualUnitaryGroupRepresentation G) :
    UnitaryVirtualRealization.FiniteUnitaryVirtualRepresentation.LightIndexEquiv
      (ActualUnitaryGroupRepresentation.blockMassMap
        (positive target) (negative target) P)
      ((negative target).product P).unitary target where
  kernelEquiv :=
    ActualUnitaryGroupRepresentation.kernelEquivPositive
      (positive target) (negative target) P
  cokernelEquiv :=
    ActualUnitaryGroupRepresentation.cokernelEquivNegative
      (positive target) (negative target) P

/-- A unitary light-plus-heavy decomposition of arbitrary source and target
representations.  The same actual representation `paired` appears on both
sides and therefore admits an invariant mass. -/
structure BlockDecomposition
    (A B : ActualUnitaryGroupRepresentation G)
    (target : FiniteUnitaryVirtualRepresentation G) where
  paired : ActualUnitaryGroupRepresentation G
  sourceEquiv : ActualUnitaryGroupRepresentation.UnitaryEquiv A
    ((positive target).product paired)
  targetEquiv : ActualUnitaryGroupRepresentation.UnitaryEquiv B
    ((negative target).product paired)

namespace BlockDecomposition

/-- The mass map canonically determined by a unitary block decomposition. -/
def massMap
    {A B : ActualUnitaryGroupRepresentation G}
    {target : FiniteUnitaryVirtualRepresentation G}
    (d : BlockDecomposition A B target) :
    Representation.IntertwiningMap A.rho B.rho :=
  ActualUnitaryGroupRepresentation.transportedBlockMassMap
    A B (positive target) (negative target) d.paired
    d.sourceEquiv d.targetEquiv

/-- The canonical block mass has exactly the prescribed light virtual
representation. -/
def lightIndexEquiv
    {A B : ActualUnitaryGroupRepresentation G}
    {target : FiniteUnitaryVirtualRepresentation G}
    (d : BlockDecomposition A B target) :
    LightIndexEquiv d.massMap B.unitary target where
  kernelEquiv :=
    ActualUnitaryGroupRepresentation.transportedKernelEquivPositive
      A B (positive target) (negative target) d.paired
      d.sourceEquiv d.targetEquiv
  cokernelEquiv :=
    ActualUnitaryGroupRepresentation.transportedCokernelEquivNegative
      A B (positive target) (negative target) d.paired
      d.sourceEquiv d.targetEquiv

end BlockDecomposition

end FiniteUnitaryVirtualRepresentation

end

end UnitaryBlockMass
end GUT
