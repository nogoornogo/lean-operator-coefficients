import GUT.SU6.Adapters.CompactRepresentationUnitarization
import Mathlib.Analysis.Matrix.Normed

open Math

/-!
# Full compact-group unitarization for continuous SU(6) representations

The hypercharge character rigidity bridge only needs a unitary maximal-torus model, so
`CompactRepresentationUnitarization` averages over that torus.  Physical standard charge-orbit bridge
sources require a unitary action of the full ultraviolet `SU(6)`.  This file
performs the same Haar averaging over all of `SU(6)` and packages the result as
a `ContinuousUnitarySU6Representation`.

The new Hilbert space is an indexed algebraic copy of the original space.  Its
index includes both the representation and its continuity certificate, which
keeps the averaged norm instance stable.  The copy is representation-
equivalent to the original model, so no character information is changed.
-/

namespace GUT
namespace ContinuousSU6Unitarization

open CompactRepresentationUnitarization
open CompactEmbeddingClassification
open ContinuousRepresentationScope
open ContinuousUnitaryWeightDecomposition
open TopologicalSpace
open scoped Matrix.Norms.Elementwise

noncomputable section

abbrev SU6 := ActualRestriction.SU6

noncomputable instance su6MeasurableSpace : MeasurableSpace SU6 :=
  borel SU6

instance su6BorelSpace : BorelSpace SU6 :=
  ⟨rfl⟩

/-- The matrix-subtype topology makes multiplication and inversion continuous.
Mathlib does not currently export this instance for `specialUnitaryGroup`. -/
instance su6IsTopologicalGroup : IsTopologicalGroup SU6 where
  continuous_inv := by
    apply continuous_induced_rng.mpr
    change Continuous fun g : SU6 =>
      star ((g : SU6) : Matrix (Fin 6) (Fin 6) ℂ)
    exact continuous_star.comp continuous_subtype_val
  continuous_mul := by
    apply continuous_induced_rng.mpr
    exact
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)

/-- Every entry of a unitary `6 x 6` matrix has norm at most one. -/
theorem unitaryMatrix_entry_norm_le_one
    (A : Matrix (Fin 6) (Fin 6) ℂ)
    (hA : A.conjTranspose * A = 1) (i j : Fin 6) :
    ‖A i j‖ ≤ 1 := by
  let L : CompactEmbeddingClassification.EuclideanRepSpace →ₗᵢ[ℂ]
      CompactEmbeddingClassification.EuclideanRepSpace :=
    (Matrix.toEuclideanLin A).isometryOfInner
      (CompactEmbeddingClassification.unitaryMatrix_preserves_inner A hA)
  let e : CompactEmbeddingClassification.EuclideanRepSpace :=
    EuclideanSpace.basisFun (Fin 6) ℂ j
  have hcoord : (L e) i = A i j := by
    simp [L, e, Matrix.mulVec]
  rw [← hcoord]
  calc
    ‖(L e) i‖ ≤ ‖L e‖ := PiLp.norm_apply_le _ _
    _ = ‖e‖ := L.norm_map e
    _ = 1 :=
      OrthonormalBasis.norm_eq_one (EuclideanSpace.basisFun (Fin 6) ℂ) j

theorem specialUnitaryGroup_isClosed :
    IsClosed (Matrix.specialUnitaryGroup (Fin 6) ℂ :
      Set (Matrix (Fin 6) (Fin 6) ℂ)) := by
  rw [show (Matrix.specialUnitaryGroup (Fin 6) ℂ :
      Set (Matrix (Fin 6) (Fin 6) ℂ)) =
      {A | star A * A = 1} ∩ {A | A.det = 1} by
    ext A
    simp [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']]
  exact
    (isClosed_eq (continuous_id.star.mul continuous_id)
      continuous_const).inter
      (isClosed_eq continuous_id.matrix_det continuous_const)

theorem specialUnitaryGroup_isBounded :
    Bornology.IsBounded
      (Matrix.specialUnitaryGroup (Fin 6) ℂ :
        Set (Matrix (Fin 6) (Fin 6) ℂ)) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨1, ?_⟩
  intro A hA
  change dist A 0 ≤ 1
  simpa [dist_eq_norm] using
    ((Matrix.norm_le_iff zero_le_one).2 (fun i j =>
      unitaryMatrix_entry_norm_le_one A (by
        simpa [Matrix.star_eq_conjTranspose] using
          (Matrix.mem_unitaryGroup_iff'.mp
            (Matrix.specialUnitaryGroup_le_unitaryGroup hA))) i j))

/-- The concrete special-unitary matrix group is compact. -/
theorem specialUnitaryGroup_isCompact :
    IsCompact (Matrix.specialUnitaryGroup (Fin 6) ℂ :
      Set (Matrix (Fin 6) (Fin 6) ℂ)) :=
  Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨specialUnitaryGroup_isClosed, specialUnitaryGroup_isBounded⟩

noncomputable instance su6CompactSpace : CompactSpace SU6 :=
  isCompact_iff_compactSpace.mp specialUnitaryGroup_isCompact

variable {E : Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- A fresh copy of a continuous representation space carrying the Hermitian
form averaged over the full compact group `SU(6)`. -/
structure HaarSU6Copy
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) where
  val : E

namespace HaarSU6Copy

def equiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    HaarSU6Copy rho hContinuous ≃ E where
  toFun := val
  invFun := mk
  left_inv v := by cases v; rfl
  right_inv _ := rfl

instance (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    AddCommGroup (HaarSU6Copy rho hContinuous) :=
  (equiv rho hContinuous).addCommGroup

def addEquiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    HaarSU6Copy rho hContinuous ≃+ E :=
  Equiv.addEquiv (equiv rho hContinuous)

instance (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Module ℂ (HaarSU6Copy rho hContinuous) :=
  (addEquiv rho hContinuous).module ℂ

def linearEquiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    HaarSU6Copy rho hContinuous ≃ₗ[ℂ] E :=
  (addEquiv rho hContinuous).linearEquiv ℂ

instance (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    FiniteDimensional ℂ (HaarSU6Copy rho hContinuous) :=
  FiniteDimensional.of_injective
    (linearEquiv rho hContinuous).toLinearMap
    (linearEquiv rho hContinuous).injective

omit [FiniteDimensional ℂ E] in
@[simp]
theorem linearEquiv_apply
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho)
    (v : HaarSU6Copy rho hContinuous) :
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
    (0 : HaarSU6Copy rho hContinuous).val = 0 :=
  rfl

/-- The full-group Haar-averaged Hermitian core on the indexed copy. -/
@[instance_reducible]
def innerCore
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    InnerProductSpace.Core ℂ (HaarSU6Copy rho hContinuous) where
  inner v w := averagedInner rho v.val w.val
  conj_inner_symm := by
    intro v w
    exact averagedInner_conj_symm rho w.val v.val
  re_inner_nonneg := by
    intro v
    exact averagedInner_re_nonneg rho hContinuous v.val
  add_left := by
    intro u v w
    exact averagedInner_add_left rho hContinuous u.val v.val w.val
  smul_left := by
    intro u v c
    exact averagedInner_smul_left rho u.val v.val c
  definite := by
    intro v hv
    apply (linearEquiv rho hContinuous).injective
    simpa using averagedInner_definite rho hContinuous v.val hv

noncomputable instance instNormedAddCommGroup
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    NormedAddCommGroup (HaarSU6Copy rho hContinuous) := by
  letI : InnerProductSpace.Core ℂ (HaarSU6Copy rho hContinuous) :=
    innerCore rho hContinuous
  exact InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := HaarSU6Copy rho hContinuous)

noncomputable instance instInnerProductSpace
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    InnerProductSpace ℂ (HaarSU6Copy rho hContinuous) := by
  letI : InnerProductSpace.Core ℂ (HaarSU6Copy rho hContinuous) :=
    innerCore rho hContinuous
  exact InnerProductSpace.ofCore (innerCore rho hContinuous).toCore

/-- The original action transported to the full-group averaged copy. -/
def representation
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Representation ℂ SU6 (HaarSU6Copy rho hContinuous) where
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
    (g : SU6) (v : HaarSU6Copy rho hContinuous) :
    representation rho hContinuous g v = ⟨rho g v.val⟩ :=
  rfl

/-- The original action and its full-group averaged copy are algebraically
equivalent. -/
def representationEquiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Representation.Equiv rho (representation rho hContinuous) :=
  Representation.Equiv.mk (linearEquiv rho hContinuous).symm (by
    intro g
    ext v
    rfl)

theorem linearEquiv_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous
      (linearEquiv rho hContinuous : HaarSU6Copy rho hContinuous → E) :=
  LinearMap.continuous_of_finiteDimensional
    (linearEquiv rho hContinuous).toLinearMap

theorem linearEquiv_symm_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous
      ((linearEquiv rho hContinuous).symm :
        E → HaarSU6Copy rho hContinuous) :=
  LinearMap.continuous_of_finiteDimensional
    (linearEquiv rho hContinuous).symm.toLinearMap

def inputMap
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    SU6 × HaarSU6Copy rho hContinuous → SU6 × E :=
  fun p => (p.1, linearEquiv rho hContinuous p.2)

theorem inputMap_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous (inputMap rho hContinuous) :=
  continuous_fst.prodMk
    ((linearEquiv_continuous rho hContinuous).comp continuous_snd)

def transportedAction
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    SU6 × HaarSU6Copy rho hContinuous → HaarSU6Copy rho hContinuous :=
  ((linearEquiv rho hContinuous).symm : E → HaarSU6Copy rho hContinuous) ∘
    (fun p : SU6 × E => rho p.1 p.2) ∘
      inputMap rho hContinuous

theorem transportedAction_continuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous (transportedAction rho hContinuous) := by
  unfold transportedAction
  exact (linearEquiv_symm_continuous rho hContinuous).comp <|
    Continuous.comp hContinuous (inputMap_continuous rho hContinuous)

/-- Joint continuity survives transport to the averaged Hilbert-space copy. -/
theorem jointlyContinuous
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    IsJointlyContinuous (representation rho hContinuous) := by
  have hActionEq :
      (fun p : SU6 × HaarSU6Copy rho hContinuous =>
        representation rho hContinuous p.1 p.2) =
      transportedAction rho hContinuous := by
    funext p
    rfl
  rw [IsJointlyContinuous, hActionEq]
  exact transportedAction_continuous rho hContinuous

omit [FiniteDimensional ℂ E] in
/-- Haar invariance makes the transported full `SU(6)` action unitary. -/
theorem unitary
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    IsUnitaryRepresentation (representation rho hContinuous) := by
  intro g v w
  change averagedInner rho (rho g v.val) (rho g w.val) =
    averagedInner rho v.val w.val
  exact averagedInner_invariant rho g v.val w.val

end HaarSU6Copy

/-- Full compact-group Haar averaging upgrades any finite-dimensional jointly
continuous `SU(6)` representation to an equivalent continuous-unitary model. -/
def model
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    ContinuousUnitarySU6Representation where
  V := HaarSU6Copy rho hContinuous
  rho := HaarSU6Copy.representation rho hContinuous
  unitary := HaarSU6Copy.unitary rho hContinuous
  continuous_action := HaarSU6Copy.jointlyContinuous rho hContinuous

/-- The unitarized model has the same algebraic representation and hence the
same character as the supplied continuous model. -/
def modelEquiv
    (rho : Representation ℂ SU6 E)
    (hContinuous : IsJointlyContinuous rho) :
    Representation.Equiv rho (model rho hContinuous).rho :=
  HaarSU6Copy.representationEquiv rho hContinuous

/-- Structure-level version of full compact-group unitarization. -/
def ofContinuous
    (R : CompactRepresentationUnitarization.ContinuousSU6Representation) :
    ContinuousUnitarySU6Representation :=
  model R.rho R.continuous_action

/-- The structure-level unitarization is representation-equivalent to its
input. -/
def ofContinuousEquiv
    (R : CompactRepresentationUnitarization.ContinuousSU6Representation) :
    Representation.Equiv R.rho (ofContinuous R).rho :=
  modelEquiv R.rho R.continuous_action

end
end ContinuousSU6Unitarization
end GUT
