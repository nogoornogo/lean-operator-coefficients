import Physics.StandardModel.Operators.Selection.AbelianProtonCharacter
import GUT.SU6.Characters.ContinuousUnitaryWeightDecomposition
import Math.RepresentationTheory.Decomposition.FiniteSemisimpleDecomposition
import GUT.SU6.SelectionRules.StandardBranch.StandardPhysicalSource
import Mathlib.Algebra.DirectSum.LinearMap

open Physics

open Math

/-!
# Unitary Abelian charge sectors commuting with SU(6)

For an ordinary Abelian symmetry, physical charges are characters of the
residual group, not elements of the residual group itself.  This file
keeps those two notions separate.  It defines the simultaneous character
eigenspace of a unitary Abelian action and proves that this whole eigenspace is
an `SU(6)` subrepresentation whenever the two actions commute.

Individual one-dimensional summands of a semisimple decomposition need not be
`SU(6)`-stable: `SU(6)` can mix repeated copies of the same residual-group
character.  The full character eigenspace is the correct source sector.
-/

namespace GUT
namespace FiniteAbelianChargeSectors
open Physics.FiniteAbelianChargeSectors
open Math.FiniteAbelianChargeSectors

open CompactEmbeddingClassification ContinuousRepresentationScope
open FiniteSemisimpleDecomposition
open StandardBranchProtonObstruction StandardPhysicalSource

noncomputable section

abbrev SU6 := ActualRestriction.SU6

/-- In any Abelian character group, the additive standard charge-orbit bridge-to-Abelian proton-operator neutrality conclusion says
that both physical proton-operator characters are trivial. -/
theorem residual_protonCharacters_eq_one
    {H : Type*} [CommGroup H]
    (S : StandardPhysicalSource.PureSMChargedSource (ChargeLabel H)) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 := by
  obtain ⟨hFirst, hSecond⟩ := S.proton_functionals_eq_zero
  exact ⟨protonFirstCharacter_eq_one_of_eq_zero S.charges hFirst,
    protonSecondCharacter_eq_one_of_eq_zero S.charges hSecond⟩

/-- Pointwise form of the Abelian residual selection rule. -/
theorem residual_protonPhases_eq_one
    {H : Type*} [CommGroup H]
    (S : StandardPhysicalSource.PureSMChargedSource (ChargeLabel H))
    (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 := by
  obtain ⟨hFirst, hSecond⟩ := residual_protonCharacters_eq_one S
  exact ⟨congrArg (fun chi : H →* Circle => chi h) hFirst,
    congrArg (fun chi : H →* Circle => chi h) hSecond⟩

/-- For a finite Abelian residual group, the additive standard charge-orbit bridge-to-Abelian proton-operator neutrality conclusion is
exactly the statement that both physical proton-operator characters are
trivial. -/
theorem finiteResidual_protonCharacters_eq_one
    {H : Type*} [CommGroup H] [Finite H]
    (S : StandardPhysicalSource.PureSMChargedSource (ChargeLabel H)) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  residual_protonCharacters_eq_one S

/-- Pointwise form of the finite residual selection rule. -/
theorem finiteResidual_protonPhases_eq_one
    {H : Type*} [CommGroup H] [Finite H]
    (S : StandardPhysicalSource.PureSMChargedSource (ChargeLabel H))
    (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  residual_protonPhases_eq_one S h

/-- A unitary Abelian action on the same Hilbert space as an `SU(6)` source,
required to commute with the full ultraviolet `SU(6)` action. -/
structure CommutingAction
    (H : Type*) [CommGroup H]
    (R : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation) where
  rho : Representation ℂ H R.V
  unitary : IsUnitaryRepresentation rho
  commutes : ∀ h g, rho h * R.rho g = R.rho g * rho h

namespace CommutingAction

variable {H : Type*} [CommGroup H]
variable {R : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation}

/-- The full simultaneous eigenspace carrying the residual-group character
`chi`. -/
def characterSubmodule (S : CommutingAction H R) (chi : H →* Circle) :
    Submodule ℂ R.V where
  carrier := {v | ∀ h, S.rho h v = (chi h : ℂ) • v}
  zero_mem' := by intro h; simp
  add_mem' := by
    intro v w hv hw h
    rw [map_add, hv h, hw h, smul_add]
  smul_mem' := by
    intro c v hv h
    rw [map_smul, hv h, smul_comm]

@[simp]
theorem mem_characterSubmodule_iff
    (S : CommutingAction H R) (chi : H →* Circle) (v : R.V) :
    v ∈ S.characterSubmodule chi ↔
      ∀ h, S.rho h v = (chi h : ℂ) • v :=
  Iff.rfl

/-- Commutation with `SU(6)` makes every full finite-character eigenspace an
`SU(6)`-invariant subspace. -/
def characterSubrepresentation
    (S : CommutingAction H R) (chi : H →* Circle) :
    Subrepresentation R.rho where
  toSubmodule := S.characterSubmodule chi
  apply_mem_toSubmodule g v hv := by
    intro h
    calc
      S.rho h (R.rho g v) = (S.rho h * R.rho g) v := rfl
      _ = (R.rho g * S.rho h) v := by rw [S.commutes h g]
      _ = R.rho g (S.rho h v) := rfl
      _ = R.rho g ((chi h : ℂ) • v) := by rw [hv h]
      _ = (chi h : ℂ) • R.rho g v := by rw [map_smul]

/-- A character sector inherits the unitary `SU(6)` action. -/
theorem characterSubrepresentation_unitary
    (S : CommutingAction H R) (chi : H →* Circle) :
    IsUnitaryRepresentation (S.characterSubrepresentation chi).toRepresentation := by
  intro g v w
  exact R.unitary g v w

/-- A character sector inherits joint continuity of the `SU(6)`
action. -/
theorem characterSubrepresentation_jointlyContinuous
    (S : CommutingAction H R) (chi : H →* Circle) :
    IsJointlyContinuous (S.characterSubrepresentation chi).toRepresentation :=
  R.continuous_action.subrepresentation (S.characterSubrepresentation chi)

/-- Every character sector is itself a physically scoped continuous
unitary `SU(6)` representation. -/
def characterSector
    (S : CommutingAction H R) (chi : H →* Circle) :
    ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation where
  V := (S.characterSubrepresentation chi).toSubmodule
  rho := (S.characterSubrepresentation chi).toRepresentation
  unitary := S.characterSubrepresentation_unitary chi
  continuous_action := S.characterSubrepresentation_jointlyContinuous chi

/-!
## Simple unitary Abelian blocks lie in character sectors
-/

/-- A finite-dimensional unitary Abelian action is semisimple by orthogonal
complements; no finiteness assumption on the group is needed. -/
theorem isSemisimpleRepresentation (S : CommutingAction H R) :
    Representation.IsSemisimpleRepresentation S.rho :=
  isSemisimpleRepresentation_of_unitary S.rho S.unitary

abbrev Block
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks) :=
  (D.subrepresentation i).toSubmodule

theorem blockFiniteDimensional
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks) :
    FiniteDimensional ℂ (Block S D i) :=
  FiniteDimensional.of_injective
    (D.subrepresentation i).toSubmodule.subtype
    (D.subrepresentation i).toSubmodule.subtype_injective

/-- Every simple block of a unitary Abelian representation is
one-dimensional. -/
theorem block_finrank_eq_one
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks) :
    Module.finrank ℂ (Block S D i) = 1 := by
  let : FiniteDimensional ℂ (Block S D i) :=
    blockFiniteDimensional S D i
  let : Representation.IsIrreducible
      (D.subrepresentation i).toRepresentation :=
    D.subrepresentation_isIrreducible i
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    (D.subrepresentation i).toRepresentation

/-- The Abelian action on a simple block remains unitary. -/
theorem blockRepresentation_unitary
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks) :
    IsUnitaryRepresentation (D.subrepresentation i).toRepresentation := by
  intro h v w
  exact S.unitary h v w

/-- The circle-valued character carried by one simple unitary block. -/
def blockCharacter
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks) : H →* Circle := by
  letI : TopologicalSpace H := ⊥
  letI : FiniteDimensional ℂ (Block S D i) :=
    blockFiniteDimensional S D i
  exact OneDimensionalUnitaryCharacter.circleMonoidHom
    (D.subrepresentation i).toRepresentation
    (block_finrank_eq_one S D i)
    (blockRepresentation_unitary S D i)

/-- The abstract block action has the same scalar as its ambient invariant
subspace realization. -/
theorem blockRepresentation_action
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks)
    (h : H) (v : D.block i) :
    D.blockRepresentation i h v =
      OneDimensionalUnitaryCharacter.scalar
          (D.subrepresentation i).toRepresentation
          (block_finrank_eq_one S D i) h • v := by
  let : TopologicalSpace H := ⊥
  let : FiniteDimensional ℂ (Block S D i) :=
    blockFiniteDimensional S D i
  let e := D.blockAmbientEquiv i
  apply e.toLinearEquiv.injective
  calc
    e.toLinearEquiv (D.blockRepresentation i h v) =
        (D.subrepresentation i).toRepresentation h
          (e.toLinearEquiv v) :=
      Representation.IntertwiningMap.isIntertwining
        (D.blockRepresentation i)
        (D.subrepresentation i).toRepresentation
        e.toIntertwiningMap h v
    _ = OneDimensionalUnitaryCharacter.scalar
          (D.subrepresentation i).toRepresentation
          (block_finrank_eq_one S D i) h • e.toLinearEquiv v := by
      rw [OneDimensionalUnitaryCharacter.action_apply]
    _ = e.toLinearEquiv
        (OneDimensionalUnitaryCharacter.scalar
          (D.subrepresentation i).toRepresentation
          (block_finrank_eq_one S D i) h • v) := by
      rw [map_smul]

/-- Character-valued form of the scalar block action. -/
theorem blockRepresentation_action_eq_character
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks)
    (h : H) (v : D.block i) :
    D.blockRepresentation i h v =
      ((S.blockCharacter D i h : Circle) : ℂ) • v := by
  let : TopologicalSpace H := ⊥
  exact blockRepresentation_action S D i h v

/-- The product representation acts coordinatewise on a one-coordinate
vector of the finite direct sum. -/
theorem directSumRepresentation_single
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (h : H)
    (i : Fin D.numberOfBlocks) (v : D.block i) :
    D.directSumRepresentation h (DFinsupp.single i v) =
      DFinsupp.single i (D.blockRepresentation i h v) := by
  apply DFinsupp.ext
  intro j
  change
    D.blockRepresentation j h
        ((DFinsupp.single (β := fun k => D.block k) i v) j) =
      (DFinsupp.single (β := fun k => D.block k) i
        (D.blockRepresentation i h v)) j
  by_cases hji : j = i
  · subst j
    rw [DFinsupp.single_eq_same, DFinsupp.single_eq_same]
  · rw [DFinsupp.single_eq_of_ne hji,
      DFinsupp.single_eq_of_ne hji, map_zero]

/-- Transporting one abstract simple block through the decomposition
equivalence lands in the full ambient eigenspace for its residual-group
character. -/
theorem inverse_single_mem_characterSubmodule
    (S : CommutingAction H R)
    (D : Decomposition S.rho) (i : Fin D.numberOfBlocks)
    (v : D.block i) :
    D.representationEquivDirectSum.toLinearEquiv.symm
        (DFinsupp.single i v) ∈
      S.characterSubmodule (S.blockCharacter D i) := by
  intro h
  let : TopologicalSpace H := ⊥
  let : FiniteDimensional ℂ (Block S D i) :=
    blockFiniteDimensional S D i
  let e := D.representationEquivDirectSum
  let c := OneDimensionalUnitaryCharacter.scalar
    (D.subrepresentation i).toRepresentation
      (block_finrank_eq_one S D i) h
  calc
    S.rho h (e.toLinearEquiv.symm (DFinsupp.single i v)) =
        e.toLinearEquiv.symm
          (D.directSumRepresentation h (DFinsupp.single i v)) := by
      exact (Representation.IntertwiningMap.isIntertwining
        D.directSumRepresentation S.rho e.symm.toIntertwiningMap h
        (DFinsupp.single i v)).symm
    _ = e.toLinearEquiv.symm
        (DFinsupp.single i (D.blockRepresentation i h v)) := by
      rw [directSumRepresentation_single S D h i v]
    _ = e.toLinearEquiv.symm (DFinsupp.single i (c • v)) := by
      rw [blockRepresentation_action S D i h v]
    _ = c • e.toLinearEquiv.symm (DFinsupp.single i v) := by
      rw [DFinsupp.single_smul, map_smul]
    _ = ((S.blockCharacter D i h : Circle) : ℂ) •
        e.toLinearEquiv.symm (DFinsupp.single i v) := by
      rfl

/-- A chosen semisimple decomposition is covered by its finite collection of
full character sectors. -/
theorem iSup_characterSubmodule_eq_top
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    (⨆ i : Fin D.numberOfBlocks,
      S.characterSubmodule (S.blockCharacter D i)) = ⊤ := by
  apply top_unique
  intro v _hv
  let e := D.representationEquivDirectSum
  let w := e.toLinearEquiv v
  have hw : v = ∑ i : Fin D.numberOfBlocks,
      e.toLinearEquiv.symm (DFinsupp.single i (w i)) := by
    apply e.toLinearEquiv.injective
    rw [map_sum]
    simp only [e.toLinearEquiv.apply_symm_apply]
    apply DFinsupp.ext
    intro j
    simp [w]
  rw [hw]
  apply Submodule.sum_mem
  intro i _hi
  apply Submodule.mem_iSup_of_mem i
  exact inverse_single_mem_characterSubmodule S D i (w i)

/-!
## Distinct and active character sectors
-/

/-- Eigenspaces for two distinct residual-group characters have zero
intersection. -/
theorem characterSubmodule_disjoint_of_ne
    (S : CommutingAction H R) {chi psi : H →* Circle}
    (hne : chi ≠ psi) :
    Disjoint (S.characterSubmodule chi) (S.characterSubmodule psi) := by
  rw [Submodule.disjoint_def]
  intro v hvChi hvPsi
  have hExists : ∃ h : H, chi h ≠ psi h := by
    by_contra hNo
    apply hne
    apply MonoidHom.ext
    intro h
    exact not_ne_iff.mp (not_exists.mp hNo h)
  obtain ⟨h, hh⟩ := hExists
  have hCoe : ((chi h : Circle) : ℂ) ≠ ((psi h : Circle) : ℂ) := by
    intro heq
    exact hh (Subtype.ext heq)
  have hSmul :
      (((chi h : Circle) : ℂ) - ((psi h : Circle) : ℂ)) • v = 0 := by
    rw [sub_smul, ← hvChi h, ← hvPsi h, sub_self]
  exact (smul_eq_zero.mp hSmul).resolve_left (sub_ne_zero.mpr hCoe)

/-- In decomposition coordinates, a vector in one character sector has zero
component in every block carrying a different character. -/
theorem decomposition_coordinate_eq_zero_of_mem_of_ne
    (S : CommutingAction H R) (D : Decomposition S.rho)
    {chi : H →* Circle} (v : R.V)
    (hv : v ∈ S.characterSubmodule chi)
    (i : Fin D.numberOfBlocks)
    (hne : S.blockCharacter D i ≠ chi) :
    (D.representationEquivDirectSum.toLinearEquiv v) i = 0 := by
  have hExists : ∃ h : H, S.blockCharacter D i h ≠ chi h := by
    by_contra hNo
    apply hne
    apply MonoidHom.ext
    intro h
    exact not_ne_iff.mp (not_exists.mp hNo h)
  obtain ⟨h, hh⟩ := hExists
  let e := D.representationEquivDirectSum
  let w := e.toLinearEquiv v
  have hIntertwines :=
    Representation.IntertwiningMap.isIntertwining
      S.rho D.directSumRepresentation e.toIntertwiningMap h v
  have hCoordinate := congrArg (fun z => z i) hIntertwines
  change
    (e.toLinearEquiv (S.rho h v)) i =
      D.blockRepresentation i h ((e.toLinearEquiv v) i) at hCoordinate
  let a : ℂ := (chi h : ℂ)
  let b : ℂ := (S.blockCharacter D i h : ℂ)
  have hEigen' : a • w i = D.blockRepresentation i h (w i) := by
    simpa [a, w, hv h, map_smul] using hCoordinate
  have hEigen : a • w i = b • w i := by
    rw [hEigen', blockRepresentation_action_eq_character S D i h]
  have hCoe : a ≠ b := by
    intro heq
    exact hh (Subtype.ext heq.symm)
  have hSmul : (a - b) • w i = 0 := by
    calc
      (a - b) • w i = a • w i - b • w i := by
        exact sub_smul a b (w i)
      _ = b • w i - b • w i := by rw [hEigen]
      _ = 0 := sub_self _
  exact (smul_eq_zero.mp hSmul).resolve_left (sub_ne_zero.mpr hCoe)

/-- The finite set of characters which occur among the blocks of a chosen
semisimple decomposition. -/
def activeCharacters
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    Finset (H →* Circle) := by
  classical
  exact Finset.univ.image (fun i => S.blockCharacter D i)

@[simp]
theorem blockCharacter_mem_activeCharacters
    (S : CommutingAction H R) (D : Decomposition S.rho)
    (i : Fin D.numberOfBlocks) :
    S.blockCharacter D i ∈ S.activeCharacters D := by
  classical
  simp [activeCharacters]

/-- The sectors indexed by the distinct active characters still span the
whole source representation. -/
theorem iSup_activeCharacterSubmodule_eq_top
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    (⨆ chi : ↥(S.activeCharacters D),
      S.characterSubmodule chi.1) = ⊤ := by
  apply top_unique
  have hBlocks :
      (⨆ i : Fin D.numberOfBlocks,
          S.characterSubmodule (S.blockCharacter D i)) ≤
        (⨆ chi : ↥(S.activeCharacters D),
          S.characterSubmodule chi.1) := by
    apply iSup_le
    intro i
    let chi : ↥(S.activeCharacters D) :=
      ⟨S.blockCharacter D i, S.blockCharacter_mem_activeCharacters D i⟩
    exact le_iSup_of_le chi le_rfl
  rw [S.iSup_characterSubmodule_eq_top D] at hBlocks
  exact hBlocks

/-- Distinct active characters index pairwise disjoint eigenspaces. -/
theorem activeCharacterSubmodule_pairwiseDisjoint
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    Pairwise (fun chi psi : ↥(S.activeCharacters D) =>
      Disjoint (S.characterSubmodule chi.1)
        (S.characterSubmodule psi.1)) := by
  intro chi psi hne
  apply S.characterSubmodule_disjoint_of_ne
  intro heq
  apply hne
  exact Subtype.ext heq

/-- The full eigenspaces indexed by the distinct active characters form an
independent family.  The proof uses the coordinate-vanishing theorem rather
than the generally insufficient pairwise-disjoint criterion. -/
theorem activeCharacterSubmodule_iSupIndep
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    iSupIndep (fun chi : ↥(S.activeCharacters D) =>
      S.characterSubmodule chi.1) := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro chars values hValues hSum chi hChi
  let e := D.representationEquivDirectSum
  apply e.toLinearEquiv.injective
  rw [map_zero]
  apply DFinsupp.ext
  intro i
  by_cases hLabel : S.blockCharacter D i = chi.1
  · have hCoordinateSum :
        ∑ psi ∈ chars, (e.toLinearEquiv (values psi)) i = 0 := by
      have hMapped := congrArg e.toLinearEquiv hSum
      have hAt := congrArg (fun z => z i) hMapped
      simpa [map_sum] using hAt
    rw [Finset.sum_eq_single chi] at hCoordinateSum
    · exact hCoordinateSum
    · intro psi hPsi hPsiNe
      apply decomposition_coordinate_eq_zero_of_mem_of_ne S D
        (values psi) (hValues psi hPsi) i
      intro hEq
      apply hPsiNe
      apply Subtype.ext
      exact hEq.symm.trans hLabel
    · exact fun hNotMem => (hNotMem hChi).elim
  · exact decomposition_coordinate_eq_zero_of_mem_of_ne S D
      (values chi) (hValues chi hChi) i hLabel

/-!
## Finite indexing and the induced charged source
-/

/-- A canonical finite index type for the distinct active characters. -/
abbrev NumberOfActiveCharacters
    (S : CommutingAction H R) (D : Decomposition S.rho) :=
  Fintype.card ↥(S.activeCharacters D)

/-- Noncomputably enumerate the finite set of active characters. -/
def activeCharacterEquiv
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    Fin (NumberOfActiveCharacters S D) ≃ ↥(S.activeCharacters D) :=
  (Fintype.equivFin ↥(S.activeCharacters D)).symm

def indexedCharacter
    (S : CommutingAction H R) (D : Decomposition S.rho)
    (i : Fin (NumberOfActiveCharacters S D)) : H →* Circle :=
  (S.activeCharacterEquiv D i).1

def indexedCharacterSubmodule
    (S : CommutingAction H R) (D : Decomposition S.rho)
    (i : Fin (NumberOfActiveCharacters S D)) : Submodule ℂ R.V :=
  (S.characterSubrepresentation (S.indexedCharacter D i)).toSubmodule

theorem indexedCharacterSubmodule_iSupIndep
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    iSupIndep (S.indexedCharacterSubmodule D) := by
  have h := S.activeCharacterSubmodule_iSupIndep D
  exact h.comp (S.activeCharacterEquiv D).injective

theorem iSup_indexedCharacterSubmodule_eq_top
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    (⨆ i, S.indexedCharacterSubmodule D i) = ⊤ := by
  apply le_antisymm le_top
  rw [← S.iSup_activeCharacterSubmodule_eq_top D]
  apply iSup_le
  intro chi
  obtain ⟨i, rfl⟩ := (S.activeCharacterEquiv D).surjective chi
  exact le_iSup (S.indexedCharacterSubmodule D) i

/-- The finitely indexed active character sectors form an internal direct sum. -/
theorem indexedCharacterSubmodule_isInternal
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    DirectSum.IsInternal (S.indexedCharacterSubmodule D) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (S.indexedCharacterSubmodule_iSupIndep D)
    (S.iSup_indexedCharacterSubmodule_eq_top D)

/-- The direct sum of the `SU(6)` representations on all active charge
sectors. -/
def sectorDirectSumRepresentation
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    Representation ℂ SU6
      (Π₀ i : Fin (NumberOfActiveCharacters S D),
        S.indexedCharacterSubmodule D i) :=
  Representation.directSum fun i =>
    (S.characterSubrepresentation (S.indexedCharacter D i)).toRepresentation

/-- Summing the character sectors recovers the original `SU(6)`
representation, not merely its dimension or its uncharged character. -/
def sectorRepresentationEquiv
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    Representation.Equiv (S.sectorDirectSumRepresentation D) R.rho where
  toLinearEquiv := LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (S.indexedCharacterSubmodule D))
    (S.indexedCharacterSubmodule_isInternal D)
  isIntertwining' g := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro v
    unfold indexedCharacterSubmodule at v ⊢
    simp only [LinearMap.comp_apply]
    change
      DirectSum.coeLinearMap
          (fun j =>
            (S.characterSubrepresentation
              (S.indexedCharacter D j)).toSubmodule)
          (DirectSum.lmap
            (fun j =>
              (S.characterSubrepresentation
                (S.indexedCharacter D j)).toRepresentation g)
            (DirectSum.lof ℂ (Fin (NumberOfActiveCharacters S D))
              (fun j => ↥(S.characterSubrepresentation
                (S.indexedCharacter D j)).toSubmodule)
              i v)) =
        R.rho g
          (DirectSum.coeLinearMap
            (fun j =>
              (S.characterSubrepresentation
                (S.indexedCharacter D j)).toSubmodule)
            (DirectSum.lof ℂ (Fin (NumberOfActiveCharacters S D))
              (fun j => ↥(S.characterSubrepresentation
                (S.indexedCharacter D j)).toSubmodule)
              i v))
    rw [DirectSum.lmap_lof, DirectSum.coeLinearMap_lof,
      DirectSum.coeLinearMap_lof]
    rfl

/-- In particular, the sum of the `SU(6)` character sectors has exactly the
same trace character as the original source representation. -/
theorem sectorDirectSum_character_eq
    (S : CommutingAction H R) (D : Decomposition S.rho) :
    (S.sectorDirectSumRepresentation D).character = R.rho.character :=
  Representation.char_iso (S.sectorRepresentationEquiv D)

/-- Every `SU(6)` action preserves each full residual-character sector. -/
theorem rho_mapsTo_indexedCharacterSubmodule
    (S : CommutingAction H R) (D : Decomposition S.rho)
    (g : SU6) (i : Fin (NumberOfActiveCharacters S D)) :
    Set.MapsTo (R.rho g) (S.indexedCharacterSubmodule D i)
      (S.indexedCharacterSubmodule D i) := by
  intro v hv
  exact
    (S.characterSubrepresentation
      (S.indexedCharacter D i)).apply_mem_toSubmodule g hv

/-- The original `SU(6)` trace is the sum of the traces on the finitely many
full Abelian character eigenspaces. -/
theorem rho_character_eq_sum_characterSector
    (S : CommutingAction H R) (D : Decomposition S.rho) (g : SU6) :
    R.rho.character g =
      ∑ i : Fin (NumberOfActiveCharacters S D),
        (S.characterSector (S.indexedCharacter D i)).rho.character g := by
  unfold Representation.character
  rw [LinearMap.trace_eq_sum_trace_restrict
    (S.indexedCharacterSubmodule_isInternal D)
    (S.rho_mapsTo_indexedCharacterSubmodule D g)]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- Convert the actual residual-group sector decomposition into the finite
charged-source format consumed by the standard charge-orbit bridge affine projection. -/
def chargedSectorSource
    (S : CommutingAction H R) (D : Decomposition S.rho)
    (coeff : ℤ) :
    StandardPhysicalSource.FiniteChargedContinuousUnitarySource
      (ChargeLabel H) :=
  List.ofFn fun i : Fin (NumberOfActiveCharacters S D) =>
    { coeff := coeff
      rep := S.characterSector (S.indexedCharacter D i)
      offset := Additive.ofMul (S.indexedCharacter D i) }

/-- After forgetting the residual labels, the charged-sector source has the
same coefficient-weighted restricted character as the original `SU(6)`
summand. -/
theorem chargedSectorSource_restrictedCharacter_eq
    (S : CommutingAction H R) (D : Decomposition S.rho)
    (coeff : ℤ) (t : AmbientLaurent.DiagonalPoint) :
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        (S.chargedSectorSource D coeff).toVirtual t =
      (coeff : ℂ) * ActualRestriction.restrictedCharacter R.rho t := by
  rw [StandardPhysicalSource.FiniteChargedContinuousUnitarySource.finiteVirtualRestrictedCharacter_toVirtual_eq_sum]
  simp only [chargedSectorSource, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  rw [← Finset.mul_sum]
  exact congrArg (fun z : ℂ => (coeff : ℂ) * z)
    (S.rho_character_eq_sum_characterSector D t.toSU6).symm

/-- The charged source obtained from a commuting unitary Abelian action has a
chargewise Weyl-invariant restricted character for every central residual
character. -/
theorem chargedSectorSource_resolvedCharacter_isWeylInvariant
    (S : CommutingAction H R) (D : Decomposition S.rho)
    (coeff : ℤ) (eta : H →* Circle) :
    StandardAbelianCharge.ResolvedWeylInvariant
      ((S.chargedSectorSource D coeff).resolvedCharacter
        (centralDegreeCharge eta)) :=
  (S.chargedSectorSource D coeff).resolvedCharacter_isWeylInvariant
    (centralDegreeCharge eta)

/-- Every finite-dimensional unitary action of an Abelian residual group
commuting with `SU(6)` has finitely many full character sectors which span the
source. -/
theorem exists_finite_character_sector_cover
    (S : CommutingAction H R) :
    ∃ chars : Finset (H →* Circle),
      iSupIndep (fun chi : ↥chars =>
        S.characterSubmodule chi.1) ∧
      (⨆ chi : ↥chars, S.characterSubmodule chi.1) = ⊤ := by
  let D : Decomposition S.rho :=
    (exists_decomposition S.rho S.isSemisimpleRepresentation).some
  exact ⟨S.activeCharacters D,
    S.activeCharacterSubmodule_iSupIndep D,
    S.iSup_activeCharacterSubmodule_eq_top D⟩

end CommutingAction

end
end FiniteAbelianChargeSectors
end GUT
