import GUT.SU6.Characters.AmbientCharacterBridge
import GUT.SU6.Characters.AmbientTorus
import Math.RepresentationTheory.Decomposition.FiniteSemisimpleDecomposition
import Math.RepresentationTheory.Characters.OneDimensionalUnitaryCharacter
import GUT.SU6.Characters.WeightTheory
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.Tactic

open Math

/-!
# Integral weight decompositions of continuous unitary SU(6) representations

The restriction of a finite-dimensional unitary representation to the compact
maximal torus is semisimple.  Since that torus is commutative, every simple
constituent is one-dimensional.  Joint continuity and unitarity turn each
constituent into a continuous circle character, and the character-lattice
theorem makes its exponent integral.

This closes the actual-representation-to-finite-weight bridge for the
continuous unitary scope.  A separate unitarization bridge is still required
to transfer the result to every physically admissible continuous
finite-dimensional representation without a chosen invariant inner product.
-/

open scoped BigOperators MonoidAlgebra

namespace GUT
namespace ContinuousUnitaryWeightDecomposition

open AmbientWeightLattice
open CompactEmbeddingClassification ContinuousRepresentationScope
open FiniteSemisimpleDecomposition

noncomputable section

abbrev Torus := AmbientTorus.Torus
abbrev SU6 := ActualRestriction.SU6
abbrev DiagonalPoint := AmbientLaurent.DiagonalPoint
abbrev Poly := AmbientLaurent.Poly

/-- Restriction of an actual `SU(6)` representation to the concrete compact
maximal torus. -/
def torusRestriction
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (rho : Representation ℂ SU6 E) : Representation ℂ Torus E :=
  rho.comp (AmbientTorus.toSU6 : Torus →* SU6)

theorem torusRestriction_unitary
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (rho : Representation ℂ SU6 E)
    (hUnitary : IsUnitaryRepresentation rho) :
    IsUnitaryRepresentation (torusRestriction rho) := by
  intro x v w
  exact hUnitary (AmbientTorus.toSU6 x) v w

theorem torusRestriction_jointlyContinuous
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    IsJointlyContinuous (torusRestriction rho) :=
  hContinuous.comp AmbientTorus.toSU6

/-- A finite basis of an actual representation consisting of integral weight
vectors for the concrete compact maximal torus. -/
structure IntegerWeightBasis
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (rho : Representation ℂ SU6 E) where
  ι : Type
  [instFintype : Fintype ι]
  [instDecidableEq : DecidableEq ι]
  basis : Module.Basis ι ℂ E
  weight : ι → Exponent
  action_on_basis :
    ∀ (x : Torus) (i : ι),
      rho (AmbientTorus.toSU6 x) (basis i) =
        AmbientLaurent.Exponent.eval (weight i)
          (AmbientTorus.diagonalPoint x).toTorusVec • basis i

attribute [instance] IntegerWeightBasis.instFintype
attribute [instance] IntegerWeightBasis.instDecidableEq

namespace IntegerWeightBasis

/-- The normalized Laurent polynomial which records the finite multiset of
weights of an integral weight basis.  Repeated weights add their
multiplicities in the `Finsupp` normal form. -/
def poly
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {rho : Representation ℂ SU6 E}
    (B : IntegerWeightBasis rho) : Poly :=
  ∑ i : B.ι, Finsupp.single (B.weight i) 1

def evalAddHom (x : AmbientLaurent.TorusVec) : Poly →+ ℂ where
  toFun := fun p => AmbientLaurent.eval p x
  map_zero' := AmbientLaurent.eval_zero x
  map_add' := fun p q => AmbientLaurent.eval_add p q x

@[simp]
theorem evalAddHom_apply (x : AmbientLaurent.TorusVec) (p : Poly) :
    evalAddHom x p = AmbientLaurent.eval p x :=
  rfl

@[simp]
theorem eval_single
    (weight : Exponent) (x : AmbientLaurent.TorusVec) :
    AmbientLaurent.eval (Finsupp.single weight 1) x =
      AmbientLaurent.Exponent.eval weight x := by
  simp [AmbientLaurent.eval]

theorem eval_poly
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {rho : Representation ℂ SU6 E}
    (B : IntegerWeightBasis rho) (x : AmbientLaurent.TorusVec) :
    AmbientLaurent.eval B.poly x =
      ∑ i : B.ι, AmbientLaurent.Exponent.eval (B.weight i) x := by
  change evalAddHom x (∑ i : B.ι, Finsupp.single (B.weight i) 1) = _
  rw [map_sum]
  simp

theorem restrictedCharacter_eq_sum
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E]
    {rho : Representation ℂ SU6 E}
    (B : IntegerWeightBasis rho) (t : DiagonalPoint) :
    ActualRestriction.restrictedCharacter rho t =
      ∑ i : B.ι,
        AmbientLaurent.Exponent.eval (B.weight i) t.toTorusVec := by
  let x : Torus := AmbientTorus.ofDiagonalPoint t
  have hPoint : AmbientTorus.diagonalPoint x = t :=
    AmbientTorus.diagonalPoint_ofDiagonalPoint t
  have hGroup : AmbientTorus.toSU6 x = t.toSU6 :=
    congrArg ActualRestriction.DiagonalSU6Point.toSU6 hPoint
  have hAction : ∀ i : B.ι,
      rho t.toSU6 (B.basis i) =
        AmbientLaurent.Exponent.eval (B.weight i) t.toTorusVec • B.basis i := by
    intro i
    simpa [hPoint, hGroup] using B.action_on_basis x i
  simpa [ActualRestriction.restrictedCharacter, Representation.character] using
    WeightTheory.trace_eq_sum_of_basis_eigen B.basis (rho t.toSU6)
      (fun i => AmbientLaurent.Exponent.eval (B.weight i) t.toTorusVec)
      hAction

/-- An integral weight basis supplies the source-side Laurent model required
by the hypercharge character rigidity ambient-character bridge. -/
def toActualAmbientLaurentModel
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E]
    {rho : Representation ℂ SU6 E}
    (B : IntegerWeightBasis rho) :
    AmbientCharacterBridge.ActualAmbientLaurentModel rho where
  poly := B.poly
  evaluates_character := by
    intro t
    rw [AmbientLaurent.diagonalEval, B.eval_poly]
    exact (B.restrictedCharacter_eq_sum t).symm

end IntegerWeightBasis

section SemisimpleConstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]
variable (rho : Representation ℂ SU6 E)

abbrev TorusBlock
    (D : Decomposition (torusRestriction rho))
    (i : Fin D.numberOfBlocks) := (D.subrepresentation i).toSubmodule

/-- A block of a finite decomposition remains finite-dimensional over the
ground field. -/
theorem blockFiniteDimensional
    (D : Decomposition (torusRestriction rho))
    (i : Fin D.numberOfBlocks) :
    FiniteDimensional ℂ (TorusBlock rho D i) :=
  FiniteDimensional.of_injective
    (D.subrepresentation i).toSubmodule.subtype
    (D.subrepresentation i).toSubmodule.subtype_injective

theorem block_finrank_eq_one
    (D : Decomposition (torusRestriction rho))
    (i : Fin D.numberOfBlocks) :
    Module.finrank ℂ (TorusBlock rho D i) = 1 := by
  let : FiniteDimensional ℂ (TorusBlock rho D i) :=
    blockFiniteDimensional rho D i
  let : Representation.IsIrreducible
      (D.subrepresentation i).toRepresentation :=
    D.subrepresentation_isIrreducible i
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    (D.subrepresentation i).toRepresentation

omit [FiniteDimensional ℂ E] in
theorem blockRepresentation_unitary
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (i : Fin D.numberOfBlocks) :
    IsUnitaryRepresentation (D.subrepresentation i).toRepresentation := by
  intro x v w
  exact hUnitary x v w

omit [FiniteDimensional ℂ E] in
theorem blockRepresentation_jointlyContinuous
    (D : Decomposition (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho))
    (i : Fin D.numberOfBlocks) :
    IsJointlyContinuous (D.subrepresentation i).toRepresentation :=
  D.subrepresentation_jointlyContinuous i hContinuous

/-- The unique integral weight of one simple torus block. -/
def blockWeight
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho))
    (i : Fin D.numberOfBlocks) : Exponent := by
  letI : FiniteDimensional ℂ (TorusBlock rho D i) :=
    blockFiniteDimensional rho D i
  exact (OneDimensionalUnitaryCharacter.existsUnique_integerWeight
    (D.subrepresentation i).toRepresentation (block_finrank_eq_one rho D i)
    (blockRepresentation_unitary rho D hUnitary i)
    (blockRepresentation_jointlyContinuous rho D hContinuous i)).choose

theorem block_character_eq_torusCharacter
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho))
    (i : Fin D.numberOfBlocks) :
    OneDimensionalUnitaryCharacter.continuousCircleCharacter
        (D.subrepresentation i).toRepresentation
        (block_finrank_eq_one rho D i)
        (blockRepresentation_unitary rho D hUnitary i)
        (blockRepresentation_jointlyContinuous rho D hContinuous i) =
      CircleTorusCharacterLattice.torusCharacter
        (blockWeight rho D hUnitary hContinuous i) := by
  let : FiniteDimensional ℂ (TorusBlock rho D i) :=
    blockFiniteDimensional rho D i
  exact (OneDimensionalUnitaryCharacter.existsUnique_integerWeight
    (D.subrepresentation i).toRepresentation (block_finrank_eq_one rho D i)
    (blockRepresentation_unitary rho D hUnitary i)
    (blockRepresentation_jointlyContinuous rho D hContinuous i)).choose_spec.1

theorem dfinsupp_basis_apply
    {n : ℕ} {M : Fin n → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module ℂ (M i)]
    (b : ∀ i, Module.Basis Unit ℂ (M i)) (i : Fin n) :
    (DFinsupp.basis b) ⟨i, ()⟩ = DFinsupp.single i (b i ()) := by
  simp [DFinsupp.basis]

/-- The scalar on a simple block is exactly the Laurent monomial associated
to its integral compact-torus weight. -/
theorem block_scalar_eq_laurent_eval
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho))
    (i : Fin D.numberOfBlocks) (x : Torus) :
    OneDimensionalUnitaryCharacter.scalar
        (D.subrepresentation i).toRepresentation
        (block_finrank_eq_one rho D i) x =
      AmbientLaurent.Exponent.eval
        (blockWeight rho D hUnitary hContinuous i)
        (AmbientTorus.diagonalPoint x).toTorusVec := by
  let : FiniteDimensional ℂ (TorusBlock rho D i) :=
    blockFiniteDimensional rho D i
  have hCharacterAtX := congrArg
    (fun f : Torus →ₜ* Circle => ((f x : Circle) : ℂ))
    (block_character_eq_torusCharacter rho D hUnitary hContinuous i)
  rw [AmbientTorus.exponent_eval_diagonalPoint]
  change
    ((OneDimensionalUnitaryCharacter.circleValue
        (D.subrepresentation i).toRepresentation
        (block_finrank_eq_one rho D i)
        (blockRepresentation_unitary rho D hUnitary i) x : Circle) : ℂ) = _
      at hCharacterAtX
  rw [OneDimensionalUnitaryCharacter.circleValue_coe] at hCharacterAtX
  exact hCharacterAtX

/-- The canonical one-element basis of a simple torus subrepresentation. -/
def subrepresentationBasis
    (D : Decomposition (torusRestriction rho))
    (i : Fin D.numberOfBlocks) :
    Module.Basis Unit ℂ (TorusBlock rho D i) := by
  letI : FiniteDimensional ℂ (TorusBlock rho D i) :=
    blockFiniteDimensional rho D i
  exact Module.basisUnique Unit (block_finrank_eq_one rho D i)

/-- Transport the one-element subrepresentation basis to the corresponding
group-algebra block used by the finite direct-sum decomposition. -/
def decompositionBlockBasis
    (D : Decomposition (torusRestriction rho))
    (i : Fin D.numberOfBlocks) :
    Module.Basis Unit ℂ (D.block i) :=
  (subrepresentationBasis rho D i).map
    (D.blockAmbientEquiv i).toLinearEquiv.symm

theorem decompositionBlockBasis_action
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho))
    (i : Fin D.numberOfBlocks) (x : Torus) :
    D.blockRepresentation i x (decompositionBlockBasis rho D i ()) =
      AmbientLaurent.Exponent.eval
          (blockWeight rho D hUnitary hContinuous i)
          (AmbientTorus.diagonalPoint x).toTorusVec •
        decompositionBlockBasis rho D i () := by
  let : FiniteDimensional ℂ (TorusBlock rho D i) :=
    blockFiniteDimensional rho D i
  let e := D.blockAmbientEquiv i
  have hBasis :
      e.toLinearEquiv (decompositionBlockBasis rho D i ()) =
        subrepresentationBasis rho D i () := by
    change (D.blockAmbientEquiv i)
        ((D.blockAmbientEquiv i).symm
          (subrepresentationBasis rho D i ())) =
      subrepresentationBasis rho D i ()
    exact (D.blockAmbientEquiv i).apply_symm_apply
      (subrepresentationBasis rho D i ())
  apply e.toLinearEquiv.injective
  calc
    e.toLinearEquiv
        (D.blockRepresentation i x (decompositionBlockBasis rho D i ())) =
      (D.subrepresentation i).toRepresentation x
        (e.toLinearEquiv (decompositionBlockBasis rho D i ())) :=
        Representation.IntertwiningMap.isIntertwining
          (D.blockRepresentation i)
          (D.subrepresentation i).toRepresentation
          e.toIntertwiningMap x (decompositionBlockBasis rho D i ())
    _ = (D.subrepresentation i).toRepresentation x
        (subrepresentationBasis rho D i ()) := by
      rw [hBasis]
    _ = OneDimensionalUnitaryCharacter.scalar
          (D.subrepresentation i).toRepresentation
          (block_finrank_eq_one rho D i) x •
        subrepresentationBasis rho D i () := by
      rw [OneDimensionalUnitaryCharacter.action_apply]
    _ = AmbientLaurent.Exponent.eval
          (blockWeight rho D hUnitary hContinuous i)
          (AmbientTorus.diagonalPoint x).toTorusVec •
        subrepresentationBasis rho D i () := by
      rw [block_scalar_eq_laurent_eval rho D hUnitary hContinuous i x]
    _ = e.toLinearEquiv
        (AmbientLaurent.Exponent.eval
            (blockWeight rho D hUnitary hContinuous i)
            (AmbientTorus.diagonalPoint x).toTorusVec •
          decompositionBlockBasis rho D i ()) := by
      rw [e.toLinearEquiv.map_smul, hBasis]

/-- The basis of the finite direct sum obtained from all one-dimensional
block bases. -/
def directSumBasis
    (D : Decomposition (torusRestriction rho)) :
    Module.Basis (Σ _i : Fin D.numberOfBlocks, Unit) ℂ
      (Π₀ i : Fin D.numberOfBlocks, D.block i) :=
  DFinsupp.basis (decompositionBlockBasis rho D)

theorem directSumBasis_action
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho))
    (x : Torus) (ix : Σ _i : Fin D.numberOfBlocks, Unit) :
    D.directSumRepresentation x (directSumBasis rho D ix) =
      AmbientLaurent.Exponent.eval
          (blockWeight rho D hUnitary hContinuous ix.1)
          (AmbientTorus.diagonalPoint x).toTorusVec •
        directSumBasis rho D ix := by
  rcases ix with ⟨i, j⟩
  have hj : j = () := Subsingleton.elim _ _
  subst j
  rw [directSumBasis, dfinsupp_basis_apply]
  apply DFinsupp.ext
  intro k
  change
    D.blockRepresentation k x
        ((DFinsupp.single ( β := fun k => D.block k) i
          (decompositionBlockBasis rho D i ())) k) =
      AmbientLaurent.Exponent.eval
          (blockWeight rho D hUnitary hContinuous i)
          (AmbientTorus.diagonalPoint x).toTorusVec •
        (DFinsupp.single (β := fun k => D.block k) i
          (decompositionBlockBasis rho D i ()) k)
  by_cases hki : k = i
  · subst k
    rw [DFinsupp.single_eq_same]
    exact decompositionBlockBasis_action rho D hUnitary hContinuous i x
  · rw [DFinsupp.single_eq_of_ne hki, map_zero, smul_zero]

/-- Transport the direct-sum weight basis back to the original representation. -/
def ambientBasis
    (D : Decomposition (torusRestriction rho)) :
    Module.Basis (Σ _i : Fin D.numberOfBlocks, Unit) ℂ E :=
  (directSumBasis rho D).map
    D.representationEquivDirectSum.toLinearEquiv.symm

theorem ambientBasis_action
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho))
    (x : Torus) (ix : Σ _i : Fin D.numberOfBlocks, Unit) :
    rho (AmbientTorus.toSU6 x) (ambientBasis rho D ix) =
      AmbientLaurent.Exponent.eval
          (blockWeight rho D hUnitary hContinuous ix.1)
          (AmbientTorus.diagonalPoint x).toTorusVec •
        ambientBasis rho D ix := by
  let e := D.representationEquivDirectSum.symm
  change torusRestriction rho x (ambientBasis rho D ix) = _
  rw [ambientBasis, Module.Basis.map_apply]
  calc
    torusRestriction rho x (e.toLinearEquiv (directSumBasis rho D ix)) =
        e.toLinearEquiv
          (D.directSumRepresentation x (directSumBasis rho D ix)) := by
      exact (Representation.IntertwiningMap.isIntertwining
        D.directSumRepresentation (torusRestriction rho)
        e.toIntertwiningMap x (directSumBasis rho D ix)).symm
    _ = e.toLinearEquiv
        (AmbientLaurent.Exponent.eval
            (blockWeight rho D hUnitary hContinuous ix.1)
            (AmbientTorus.diagonalPoint x).toTorusVec •
          directSumBasis rho D ix) := by
      rw [directSumBasis_action rho D hUnitary hContinuous x ix]
    _ = AmbientLaurent.Exponent.eval
          (blockWeight rho D hUnitary hContinuous ix.1)
          (AmbientTorus.diagonalPoint x).toTorusVec •
        e.toLinearEquiv (directSumBasis rho D ix) := by
      rw [map_smul]

/-- A chosen finite semisimple decomposition supplies an integral weight
basis of the original actual representation. -/
def integerWeightBasisOfDecomposition
    (D : Decomposition (torusRestriction rho))
    (hUnitary : IsUnitaryRepresentation (torusRestriction rho))
    (hContinuous : IsJointlyContinuous (torusRestriction rho)) :
    IntegerWeightBasis rho where
  ι := Σ _i : Fin D.numberOfBlocks, Unit
  basis := ambientBasis rho D
  weight := fun ix => blockWeight rho D hUnitary hContinuous ix.1
  action_on_basis := ambientBasis_action rho D hUnitary hContinuous

/-- Every finite-dimensional jointly continuous unitary `SU(6)`
representation has a finite integral weight basis on the maximal torus. -/
def integerWeightBasisOfContinuousUnitary
    (hUnitary : IsUnitaryRepresentation rho)
    (hContinuous : IsJointlyContinuous rho) : IntegerWeightBasis rho := by
  let rhoT := torusRestriction rho
  have hUnitaryT : IsUnitaryRepresentation rhoT :=
    torusRestriction_unitary rho hUnitary
  have hContinuousT : IsJointlyContinuous rhoT :=
    torusRestriction_jointlyContinuous rho hContinuous
  have hSemisimple : Representation.IsSemisimpleRepresentation rhoT :=
    isSemisimpleRepresentation_of_unitary rhoT hUnitaryT
  let D : Decomposition rhoT :=
    (exists_decomposition rhoT hSemisimple).some
  exact integerWeightBasisOfDecomposition rho D hUnitaryT hContinuousT

/-- Consequently, every finite-dimensional jointly continuous unitary
`SU(6)` representation has the actual normalized Laurent model required by
hypercharge character rigidity. -/
def actualAmbientLaurentModelOfContinuousUnitary
    (hUnitary : IsUnitaryRepresentation rho)
    (hContinuous : IsJointlyContinuous rho) :
    AmbientCharacterBridge.ActualAmbientLaurentModel rho :=
  (integerWeightBasisOfContinuousUnitary rho hUnitary hContinuous).toActualAmbientLaurentModel

end SemisimpleConstruction

/-!
## Transfer along a continuous unitarizable model
-/

/-- A finite-dimensional `SU(6)` representation with a chosen Hilbert-space
model for which the action is jointly continuous and unitary. -/
structure ContinuousUnitarySU6Representation where
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  [instInnerProductSpace : InnerProductSpace ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  rho : Representation ℂ SU6 V
  unitary : IsUnitaryRepresentation rho
  continuous_action : IsJointlyContinuous rho

attribute [instance]
  ContinuousUnitarySU6Representation.instNormedAddCommGroup
  ContinuousUnitarySU6Representation.instInnerProductSpace
  ContinuousUnitarySU6Representation.instFiniteDimensional

namespace ContinuousUnitarySU6Representation

def toActualRepresentation (R : ContinuousUnitarySU6Representation) :
    AmbientCharacterBridge.ActualRepresentation where
  V := R.V
  rho := R.rho

def ambientLaurentModel (R : ContinuousUnitarySU6Representation) :
    AmbientCharacterBridge.ActualAmbientLaurentModel R.rho :=
  actualAmbientLaurentModelOfContinuousUnitary R.rho
    R.unitary R.continuous_action

end ContinuousUnitarySU6Representation

/-- An ordinary actual representation together with an algebraically
equivalent continuous unitary realization.  The remaining compact-group
unitarization theorem should construct this witness from the intended
continuity assumptions. -/
structure ContinuousUnitarizableWitness
    (R : AmbientCharacterBridge.ActualRepresentation) where
  model : ContinuousUnitarySU6Representation
  equiv : Representation.Equiv R.rho model.rho

namespace ContinuousUnitarizableWitness

/-- Character equality transports the Laurent realization from the chosen
continuous unitary model back to the original actual representation. -/
def ambientLaurentModel
    {R : AmbientCharacterBridge.ActualRepresentation}
    (W : ContinuousUnitarizableWitness R) :
    AmbientCharacterBridge.ActualAmbientLaurentModel R.rho where
  poly := W.model.ambientLaurentModel.poly
  evaluates_character := by
    intro t
    calc
      AmbientLaurent.diagonalEval W.model.ambientLaurentModel.poly t =
          ActualRestriction.restrictedCharacter W.model.rho t :=
        W.model.ambientLaurentModel.evaluates_character t
      _ = ActualRestriction.restrictedCharacter R.rho t := by
        unfold ActualRestriction.restrictedCharacter
        exact (congrFun (Representation.char_iso W.equiv) t.toSU6).symm

end ContinuousUnitarizableWitness

/-- A provider of continuous unitarizable realizations for every actual
representation admitted by a chosen physical source category. -/
structure ContinuousUnitarizableProvider where
  witness : ∀ R : AmbientCharacterBridge.ActualRepresentation,
    ContinuousUnitarizableWitness R

namespace ContinuousUnitarizableProvider

def modelActual
    (P : ContinuousUnitarizableProvider)
    (R : AmbientCharacterBridge.ActualRepresentation) :
    AmbientCharacterBridge.ActualAmbientLaurentModel R.rho :=
  (P.witness R).ambientLaurentModel

def modelSummand
    (P : ContinuousUnitarizableProvider)
    (s : AmbientCharacterBridge.VirtualSummand) :
    AmbientCharacterBridge.ModeledVirtualSummand where
  coeff := s.coeff
  rep := s.rep
  poly := (P.modelActual s.rep).poly
  evaluates_rep := (P.modelActual s.rep).evaluates_character

def modelFiniteVirtual
    (P : ContinuousUnitarizableProvider) :
    AmbientCharacterBridge.FiniteVirtualRepresentation →
      AmbientCharacterBridge.ModeledFiniteVirtualRepresentation
  | [] => []
  | s :: ss => P.modelSummand s :: P.modelFiniteVirtual ss

@[simp]
theorem modelFiniteVirtual_toVirtual
    (P : ContinuousUnitarizableProvider)
    (chi : AmbientCharacterBridge.FiniteVirtualRepresentation) :
    AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtual
        (P.modelFiniteVirtual chi) = chi := by
  induction chi with
  | nil => rfl
  | cons s ss ih =>
      simp [modelFiniteVirtual,
        AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtual,
        modelSummand, AmbientCharacterBridge.ModeledVirtualSummand.toVirtualSummand,
        ih]

/-- Every finite virtual representation in a continuous-unitarizable source
category has one common faithful normalized ambient Laurent model. -/
def finiteVirtualAmbientLaurentModel
    (P : ContinuousUnitarizableProvider)
    (chi : AmbientCharacterBridge.FiniteVirtualRepresentation) :
    AmbientCharacterBridge.VirtualAmbientLaurentModel chi := by
  let M :=
    AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtualAmbientLaurentModel
      (P.modelFiniteVirtual chi)
  rw [P.modelFiniteVirtual_toVirtual chi] at M
  exact M

theorem finiteVirtual_poly_isWeylInvariant
    (P : ContinuousUnitarizableProvider)
    (chi : AmbientCharacterBridge.FiniteVirtualRepresentation) :
    AmbientWeightLattice.IsWeylInvariant
      (P.finiteVirtualAmbientLaurentModel chi).poly :=
  (P.finiteVirtualAmbientLaurentModel chi).isWeylInvariant

end ContinuousUnitarizableProvider

end
end ContinuousUnitaryWeightDecomposition
end GUT
