import Math.RepresentationTheory.Unitary.HaarAveraging
import GUT.SU6.Characters.ContinuousUnitaryWeightDecomposition
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

open Math

/-!
# Unitarizing continuous finite-dimensional representations of compact groups

For a jointly continuous representation of a compact group, average an
arbitrary Hermitian inner product against normalized left Haar measure.  The
inverse in the integrand turns invariance of the averaged form into a direct
application of left invariance.  The averaged form is positive definite and
therefore defines a new Hilbert norm.

The final construction uses `HaarTorusCopy rho hContinuous`, a fresh
algebraic copy of the representation space with no pre-existing topology.
This avoids a second, definitionally different norm on `E`.  In finite
dimension the linear equivalences between the old and averaged norms are
automatically continuous, so joint continuity transports to the unitary
torus model.  Applied to `SU(6)`, this constructs the witness required by the
hypercharge character rigidity Laurent-character bridge.
-/

open scoped ComplexConjugate

namespace GUT
namespace CompactRepresentationUnitarization
open Math.CompactRepresentationUnitarization

open CompactEmbeddingClassification ContinuousRepresentationScope
open MeasureTheory
open TopologicalSpace

noncomputable section

/-!
## A fresh normed copy and the SU(6) witness
-/

section SU6

universe u

abbrev SU6 := ActualRestriction.SU6
abbrev Torus := AmbientTorus.Torus

noncomputable instance torusMeasurableSpace : MeasurableSpace Torus :=
  borel Torus

instance torusBorelSpace : BorelSpace Torus :=
  ⟨rfl⟩

variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-!
### A globally instance-stable averaged model

Indexing the fresh copy by the representation and its continuity proof makes
the averaged norm a unique global instance.  This keeps the concrete integral
opaque when later constructions request the normed-space hierarchy.
-/

/-- The representation-indexed copy carrying the averaged torus norm. -/
structure HaarTorusCopy
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) where
  val : E

namespace HaarTorusCopy

def equiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    HaarTorusCopy rho hContinuous ≃ E where
  toFun := val
  invFun := mk
  left_inv v := by cases v; rfl
  right_inv _ := rfl

instance (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    AddCommGroup (HaarTorusCopy rho hContinuous) :=
  (equiv rho hContinuous).addCommGroup

/-- The transported additive equivalence underlying the averaged copy. -/
def addEquiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    HaarTorusCopy rho hContinuous ≃+ E :=
  Equiv.addEquiv (equiv rho hContinuous)

instance (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Module ℂ (HaarTorusCopy rho hContinuous) :=
  (addEquiv rho hContinuous).module ℂ

def linearEquiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    HaarTorusCopy rho hContinuous ≃ₗ[ℂ] E :=
  (addEquiv rho hContinuous).linearEquiv ℂ

instance (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    FiniteDimensional ℂ (HaarTorusCopy rho hContinuous) :=
  FiniteDimensional.of_injective
    (linearEquiv rho hContinuous).toLinearMap
    (linearEquiv rho hContinuous).injective

omit [FiniteDimensional ℂ E] in
@[simp]
theorem linearEquiv_apply
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho)
    (v : HaarTorusCopy rho hContinuous) :
    linearEquiv rho hContinuous v = v.val :=
  rfl

omit [FiniteDimensional ℂ E] in
@[simp]
theorem linearEquiv_symm_apply
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) (v : E) :
    (linearEquiv rho hContinuous).symm v = ⟨v⟩ :=
  rfl

omit [FiniteDimensional ℂ E] in
@[simp]
theorem val_zero
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    (0 : HaarTorusCopy rho hContinuous).val = 0 :=
  rfl

/-- The maximal-torus-averaged Hermitian core on the indexed copy. -/
@[instance_reducible]
def innerCore
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    InnerProductSpace.Core ℂ (HaarTorusCopy rho hContinuous) where
  inner v w := averagedInner
    (ContinuousUnitaryWeightDecomposition.torusRestriction rho) v.val w.val
  conj_inner_symm := by
    intro v w
    exact averagedInner_conj_symm
      (ContinuousUnitaryWeightDecomposition.torusRestriction rho) w.val v.val
  re_inner_nonneg := by
    intro v
    exact averagedInner_re_nonneg
      (ContinuousUnitaryWeightDecomposition.torusRestriction rho)
      (ContinuousUnitaryWeightDecomposition.torusRestriction_jointlyContinuous
        rho hContinuous)
      v.val
  add_left := by
    intro u v w
    exact averagedInner_add_left
      (ContinuousUnitaryWeightDecomposition.torusRestriction rho)
      (ContinuousUnitaryWeightDecomposition.torusRestriction_jointlyContinuous
        rho hContinuous)
      u.val v.val w.val
  smul_left := by
    intro u v c
    exact averagedInner_smul_left
      (ContinuousUnitaryWeightDecomposition.torusRestriction rho)
      u.val v.val c
  definite := by
    intro v hv
    apply (linearEquiv rho hContinuous).injective
    simpa using
      (averagedInner_definite
        (ContinuousUnitaryWeightDecomposition.torusRestriction rho)
        (ContinuousUnitaryWeightDecomposition.torusRestriction_jointlyContinuous
          rho hContinuous)
        v.val hv)

noncomputable instance instNormedAddCommGroup
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    NormedAddCommGroup (HaarTorusCopy rho hContinuous) := by
  letI : InnerProductSpace.Core ℂ (HaarTorusCopy rho hContinuous) :=
    innerCore rho hContinuous
  exact InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := HaarTorusCopy rho hContinuous)

noncomputable instance instInnerProductSpace
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    InnerProductSpace ℂ (HaarTorusCopy rho hContinuous) := by
  letI : InnerProductSpace.Core ℂ (HaarTorusCopy rho hContinuous) :=
    innerCore rho hContinuous
  exact InnerProductSpace.ofCore (innerCore rho hContinuous).toCore

/-- The original action transported to the indexed averaged copy. -/
def representation
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Representation ℂ SU6 (HaarTorusCopy rho hContinuous) where
  toFun g := (linearEquiv rho hContinuous).symm.toLinearMap.comp
    ((rho g).comp (linearEquiv rho hContinuous).toLinearMap)
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp [map_mul]

omit [FiniteDimensional ℂ E] in
@[simp]
theorem representation_apply
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho)
    (g : SU6) (v : HaarTorusCopy rho hContinuous) :
    representation rho hContinuous g v = ⟨rho g v.val⟩ :=
  rfl

/-- The original and averaged-copy actions are algebraically equivalent. -/
def representationEquiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Representation.Equiv rho (representation rho hContinuous) :=
  Representation.Equiv.mk (linearEquiv rho hContinuous).symm (by
    intro g
    ext v
    rfl)

/-- The comparison map from the averaged norm to the seed norm is continuous
because both spaces are finite-dimensional. -/
theorem linearEquiv_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous
      (linearEquiv rho hContinuous : HaarTorusCopy rho hContinuous → E) :=
  LinearMap.continuous_of_finiteDimensional
    (linearEquiv rho hContinuous).toLinearMap

/-- The inverse comparison map is continuous by the same finite-dimensional
topology theorem. -/
theorem linearEquiv_symm_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous
      ((linearEquiv rho hContinuous).symm :
        E → HaarTorusCopy rho hContinuous) :=
  LinearMap.continuous_of_finiteDimensional
    (linearEquiv rho hContinuous).symm.toLinearMap

/-- Feed the torus coordinate and the underlying seed-space vector into the
original action. -/
def torusInputMap
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Torus × HaarTorusCopy rho hContinuous → Torus × E :=
  fun p => (p.1, linearEquiv rho hContinuous p.2)

theorem torusInputMap_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous (torusInputMap rho hContinuous) :=
  continuous_fst.prodMk
    ((linearEquiv_continuous rho hContinuous).comp continuous_snd)

/-- The original torus action, transported through the comparison
equivalence into the averaged copy. -/
def transportedTorusAction
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Torus × HaarTorusCopy rho hContinuous → HaarTorusCopy rho hContinuous :=
  ((linearEquiv rho hContinuous).symm : E → HaarTorusCopy rho hContinuous) ∘
    (fun p : Torus × E =>
      (ContinuousUnitaryWeightDecomposition.torusRestriction rho) p.1 p.2) ∘
      torusInputMap rho hContinuous

/-- Joint continuity of the original torus action transported through the
finite-dimensional comparison equivalence. -/
theorem transportedTorusAction_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous (transportedTorusAction rho hContinuous) := by
  unfold transportedTorusAction
  exact (linearEquiv_symm_continuous rho hContinuous).comp <|
    Continuous.comp
      (ContinuousUnitaryWeightDecomposition.torusRestriction_jointlyContinuous
        rho hContinuous)
      (torusInputMap_continuous rho hContinuous)

theorem torus_jointlyContinuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    IsJointlyContinuous
      (ContinuousUnitaryWeightDecomposition.torusRestriction
        (representation rho hContinuous)) := by
  have hActionEq :
      (fun p : Torus × HaarTorusCopy rho hContinuous =>
        (ContinuousUnitaryWeightDecomposition.torusRestriction
          (representation rho hContinuous)) p.1 p.2) =
      transportedTorusAction rho hContinuous := by
    funext p
    rfl
  rw [IsJointlyContinuous, hActionEq]
  exact transportedTorusAction_continuous rho hContinuous

omit [FiniteDimensional ℂ E] in
theorem torus_unitary
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    IsUnitaryRepresentation
      (ContinuousUnitaryWeightDecomposition.torusRestriction
        (representation rho hContinuous)) := by
  let rhoT := ContinuousUnitaryWeightDecomposition.torusRestriction rho
  intro x v w
  change averagedInner rhoT (rhoT x v.val) (rhoT x w.val) =
    averagedInner rhoT v.val w.val
  exact averagedInner_invariant rhoT x v.val w.val

end HaarTorusCopy

/-- The weight-decomposition bridge only needs the maximal-torus restriction
to be continuous and unitary.  Keeping this construction separate prevents
the concrete Haar integral defining an averaged norm from being unfolded
during the semisimple-decomposition elaboration. -/
def actualAmbientLaurentModelOfUnitaryTorus
    {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F]
    (rho : Representation ℂ SU6 F)
    (hUnitaryT : IsUnitaryRepresentation
      (ContinuousUnitaryWeightDecomposition.torusRestriction rho))
    (hContinuousT : IsJointlyContinuous
      (ContinuousUnitaryWeightDecomposition.torusRestriction rho)) :
    AmbientCharacterBridge.ActualAmbientLaurentModel rho := by
  let rhoT := ContinuousUnitaryWeightDecomposition.torusRestriction rho
  have hSemisimple : Representation.IsSemisimpleRepresentation rhoT :=
    isSemisimpleRepresentation_of_unitary rhoT hUnitaryT
  let D : FiniteSemisimpleDecomposition.Decomposition rhoT :=
    (FiniteSemisimpleDecomposition.exists_decomposition rhoT hSemisimple).some
  exact
    (ContinuousUnitaryWeightDecomposition.integerWeightBasisOfDecomposition
      rho D hUnitaryT hContinuousT).toActualAmbientLaurentModel

/-- A realization equivalent to `rho` whose maximal-torus restriction is
unitary and jointly continuous.  Full `SU(6)` unitarity is unnecessary for
the hypercharge character rigidity weight-character construction. -/
structure ContinuousTorusUnitarization
    (rho : Representation ℂ SU6 E) where
  V : Type u
  [instNormedAddCommGroup : NormedAddCommGroup V]
  [instInnerProductSpace : InnerProductSpace ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  model : Representation ℂ SU6 V
  equiv : Representation.Equiv rho model
  torus_unitary : IsUnitaryRepresentation
    (ContinuousUnitaryWeightDecomposition.torusRestriction model)
  torus_continuous : IsJointlyContinuous
    (ContinuousUnitaryWeightDecomposition.torusRestriction model)

attribute [instance]
  ContinuousTorusUnitarization.instNormedAddCommGroup
  ContinuousTorusUnitarization.instInnerProductSpace
  ContinuousTorusUnitarization.instFiniteDimensional

namespace ContinuousTorusUnitarization

/-- Transfer the Laurent character of the unitary torus model back through
the algebraic representation equivalence. -/
def ambientLaurentModel
    {rho : Representation ℂ SU6 E}
    (W : ContinuousTorusUnitarization rho) :
    AmbientCharacterBridge.ActualAmbientLaurentModel rho := by
  let M := actualAmbientLaurentModelOfUnitaryTorus W.model
    W.torus_unitary W.torus_continuous
  exact {
    poly := M.poly
    evaluates_character := by
      intro t
      calc
        AmbientLaurent.diagonalEval M.poly t =
            ActualRestriction.restrictedCharacter W.model t :=
          M.evaluates_character t
        _ = ActualRestriction.restrictedCharacter rho t := by
          unfold ActualRestriction.restrictedCharacter
          exact (congrFun (Representation.char_iso W.equiv) t.toSU6).symm
  }

end ContinuousTorusUnitarization

/-- Haar averaging on the maximal torus constructs the unitary torus model
for any jointly continuous finite-dimensional `SU(6)` representation. -/
def continuousTorusUnitarizationOfContinuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    ContinuousTorusUnitarization rho where
  V := HaarTorusCopy rho hContinuous
  model := HaarTorusCopy.representation rho hContinuous
  equiv := HaarTorusCopy.representationEquiv rho hContinuous
  torus_unitary := HaarTorusCopy.torus_unitary rho hContinuous
  torus_continuous := HaarTorusCopy.torus_jointlyContinuous rho hContinuous

/-- Every jointly continuous finite-dimensional complex `SU(6)`
representation has the canonical finite Laurent character required by hypercharge character rigidity.
Only the maximal torus is averaged, since that is the unitary decomposition
needed to construct integral weights.  The input inner product is merely a
seed and is not assumed invariant. -/
def actualAmbientLaurentModelOfContinuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    AmbientCharacterBridge.ActualAmbientLaurentModel rho :=
  (continuousTorusUnitarizationOfContinuous rho hContinuous).ambientLaurentModel

/-!
## Heterogeneous finite virtual sources
-/

/-- One physically admissible hypercharge character rigidity summand: a finite-dimensional complex
`SU(6)` representation with jointly continuous action.  Its chosen seed inner
product need not be invariant. -/
structure ContinuousSU6Representation where
  V : Type
  [instNormedAddCommGroup : NormedAddCommGroup V]
  [instInnerProductSpace : InnerProductSpace ℂ V]
  [instFiniteDimensional : FiniteDimensional ℂ V]
  rho : Representation ℂ SU6 V
  continuous_action : IsJointlyContinuous rho

attribute [instance]
  ContinuousSU6Representation.instNormedAddCommGroup
  ContinuousSU6Representation.instInnerProductSpace
  ContinuousSU6Representation.instFiniteDimensional

namespace ContinuousSU6Representation

def toActualRepresentation (R : ContinuousSU6Representation) :
    AmbientCharacterBridge.ActualRepresentation where
  V := R.V
  rho := R.rho

/-- Haar averaging and torus weight theory supply the common faithful Laurent
model for every admitted continuous summand. -/
def ambientLaurentModel (R : ContinuousSU6Representation) :
    AmbientCharacterBridge.ActualAmbientLaurentModel R.rho :=
  actualAmbientLaurentModelOfContinuous R.rho R.continuous_action

end ContinuousSU6Representation

/-- An integer virtual coefficient together with an actual jointly continuous
finite-dimensional representation. -/
structure ContinuousVirtualSummand where
  coeff : ℤ
  rep : ContinuousSU6Representation

namespace ContinuousVirtualSummand

def toModeledVirtualSummand (s : ContinuousVirtualSummand) :
    AmbientCharacterBridge.ModeledVirtualSummand where
  coeff := s.coeff
  rep := s.rep.toActualRepresentation
  poly := s.rep.ambientLaurentModel.poly
  evaluates_rep := s.rep.ambientLaurentModel.evaluates_character

end ContinuousVirtualSummand

/-- The intended finite-virtual hypercharge character rigidity source scope, without a unitary hypothesis
on the supplied actions. -/
abbrev FiniteContinuousVirtualRepresentation := List ContinuousVirtualSummand

namespace FiniteContinuousVirtualRepresentation

def toModeled : FiniteContinuousVirtualRepresentation →
    AmbientCharacterBridge.ModeledFiniteVirtualRepresentation
  | [] => []
  | s :: ss => s.toModeledVirtualSummand :: toModeled ss

def toVirtual (chi : FiniteContinuousVirtualRepresentation) :
    AmbientCharacterBridge.FiniteVirtualRepresentation :=
  AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtual
    chi.toModeled

/-- Every finite integer combination of admitted continuous representations
has one normalized Laurent polynomial evaluating to its actual virtual
restricted character. -/
def ambientLaurentModel (chi : FiniteContinuousVirtualRepresentation) :
    AmbientCharacterBridge.VirtualAmbientLaurentModel chi.toVirtual :=
  AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtualAmbientLaurentModel
    chi.toModeled

/-- The resulting actual finite-virtual character is invariant under the full
ambient Weyl group; in particular it is fixed by `swap36`. -/
theorem poly_isWeylInvariant (chi : FiniteContinuousVirtualRepresentation) :
    AmbientWeightLattice.IsWeylInvariant chi.ambientLaurentModel.poly :=
  chi.ambientLaurentModel.isWeylInvariant

end FiniteContinuousVirtualRepresentation

end SU6

end
end CompactRepresentationUnitarization
end GUT
