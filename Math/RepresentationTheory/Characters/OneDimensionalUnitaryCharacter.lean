import Math.LieGroups.Torus.CircleTorusCharacterLattice
import Math.RepresentationTheory.Unitary.ContinuousAction
import Math.RepresentationTheory.Unitary.UnitaryRepresentation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Continuous unitary representations of dimension one

A one-dimensional complex representation acts by a unique scalar.  If the
representation is unitary, that scalar lies on `Circle`; if the action is
jointly continuous, the resulting circle-valued character is continuous.
Combining this with `CircleTorusCharacterLattice` identifies every simple
constituent of a continuous unitary torus representation with an integral
Laurent monomial.
-/

namespace Math
namespace OneDimensionalUnitaryCharacter

open CompactEmbeddingClassification ContinuousRepresentationScope

noncomputable section

variable {G E : Type*} [Group G] [TopologicalSpace G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

/-- The unique scalar by which a group element acts on a one-dimensional
representation. -/
def scalar (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1) (g : G) : ℂ :=
  (LinearEquiv.smul_id_of_finrank_eq_one hDimension).symm (rho g)

omit [TopologicalSpace G] in
theorem action_eq_scalar_smul_id
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1) (g : G) :
    rho g = scalar rho hDimension g • (LinearMap.id : E →ₗ[ℂ] E) := by
  exact ((LinearEquiv.smul_id_of_finrank_eq_one hDimension).apply_symm_apply
    (rho g)).symm

omit [TopologicalSpace G] in
theorem action_apply
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1) (g : G) (v : E) :
    rho g v = scalar rho hDimension g • v := by
  rw [action_eq_scalar_smul_id]
  rfl

omit [TopologicalSpace G] in
@[simp]
theorem scalar_one
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1) :
    scalar rho hDimension 1 = 1 := by
  apply (LinearEquiv.smul_id_of_finrank_eq_one hDimension).injective
  simp [scalar, Module.End.one_eq_id]

omit [TopologicalSpace G] in
theorem scalar_mul
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1) (g h : G) :
    scalar rho hDimension (g * h) =
      scalar rho hDimension g * scalar rho hDimension h := by
  apply (LinearEquiv.smul_id_of_finrank_eq_one hDimension).injective
  rw [LinearEquiv.smul_id_of_finrank_eq_one_apply]
  calc
    (scalar rho hDimension (g * h)) • (LinearMap.id : E →ₗ[ℂ] E) =
        rho (g * h) := (action_eq_scalar_smul_id rho hDimension (g * h)).symm
    _ = rho g * rho h := map_mul rho g h
    _ = (scalar rho hDimension g • (LinearMap.id : E →ₗ[ℂ] E)) *
        (scalar rho hDimension h • (LinearMap.id : E →ₗ[ℂ] E)) := by
          rw [action_eq_scalar_smul_id, action_eq_scalar_smul_id]
    _ = (scalar rho hDimension g * scalar rho hDimension h) •
        (LinearMap.id : E →ₗ[ℂ] E) := by
          ext v
          simp only [Module.End.mul_apply, LinearMap.smul_apply,
            LinearMap.id_coe, id_eq, smul_smul]

/-- The scalar action as a complex-valued monoid homomorphism. -/
def scalarMonoidHom
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1) : G →* ℂ where
  toFun := scalar rho hDimension
  map_one' := scalar_one rho hDimension
  map_mul' := scalar_mul rho hDimension

omit [TopologicalSpace G] in
theorem norm_scalar_eq_one
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1)
    (hUnitary : IsUnitaryRepresentation rho) (g : G) :
    ‖scalar rho hDimension g‖ = 1 := by
  let b : Module.Basis Unit ℂ E := Module.basisUnique Unit hDimension
  let v : E := b ()
  have hv : v ≠ 0 := b.ne_zero ()
  have hnormSq : ‖rho g v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ E _ _ _ (rho g v),
      @norm_sq_eq_re_inner ℂ E _ _ _ v, hUnitary g v v]
  rw [action_apply rho hDimension, norm_smul] at hnormSq
  have hvPos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [mul_pow] at hnormSq
  have hvSqNe : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hvPos)
  have hScalarSq : ‖scalar rho hDimension g‖ ^ 2 = 1 := by
    apply mul_right_cancel₀ hvSqNe
    simpa using hnormSq
  nlinarith [norm_nonneg (scalar rho hDimension g)]

/-- The scalar action, now regarded as a point of the unit circle. -/
def circleValue
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1)
    (hUnitary : IsUnitaryRepresentation rho) (g : G) : Circle :=
  ⟨scalar rho hDimension g, by
    simp only [Submonoid.unitSphere]
    exact mem_sphere_zero_iff_norm.2
      (norm_scalar_eq_one rho hDimension hUnitary g)⟩

omit [TopologicalSpace G] in
@[simp]
theorem circleValue_coe
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1)
    (hUnitary : IsUnitaryRepresentation rho) (g : G) :
    ((circleValue rho hDimension hUnitary g : Circle) : ℂ) =
      scalar rho hDimension g :=
  rfl

/-- The circle-valued character underlying a one-dimensional unitary
representation. -/
def circleMonoidHom
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1)
    (hUnitary : IsUnitaryRepresentation rho) : G →* Circle where
  toFun := circleValue rho hDimension hUnitary
  map_one' := by
    apply Subtype.ext
    simp [circleValue]
  map_mul' := by
    intro g h
    apply Subtype.ext
    exact scalar_mul rho hDimension g h

omit [TopologicalSpace G] in
theorem scalar_eq_basis_coordinate
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1) (g : G) :
    scalar rho hDimension g =
      (Module.basisUnique Unit hDimension).repr
        (rho g (Module.basisUnique Unit hDimension ())) () := by
  let b : Module.Basis Unit ℂ E := Module.basisUnique Unit hDimension
  have hAction := action_apply rho hDimension g (b ())
  have hCoord := congrArg (fun v : E => b.repr v ()) hAction
  simpa [b] using hCoord.symm

theorem continuous_scalar
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1)
    (hContinuous : IsJointlyContinuous rho) :
    Continuous (scalar rho hDimension) := by
  let b : Module.Basis Unit ℂ E := Module.basisUnique Unit hDimension
  let coord : E →ₗ[ℂ] ℂ :=
    (Finsupp.lapply ()).comp b.repr.toLinearMap
  have hCoord : Continuous coord := coord.continuous_of_finiteDimensional
  have hOrbit : Continuous fun g => rho g (b ()) := hContinuous.orbit (b ())
  have hComposite : Continuous fun g => coord (rho g (b ())) :=
    hCoord.comp hOrbit
  apply hComposite.congr
  intro g
  simp [coord, b, scalar_eq_basis_coordinate rho hDimension g]

/-- The one-dimensional unitary character as a continuous monoid
homomorphism. -/
def continuousCircleCharacter
    (rho : Representation ℂ G E)
    (hDimension : Module.finrank ℂ E = 1)
    (hUnitary : IsUnitaryRepresentation rho)
    (hContinuous : IsJointlyContinuous rho) : G →ₜ* Circle where
  toMonoidHom := circleMonoidHom rho hDimension hUnitary
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_scalar rho hDimension hContinuous

section FiniteTorus

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A one-dimensional continuous unitary representation of a finite compact
torus has a unique integral Laurent weight. -/
theorem existsUnique_integerWeight
    (rho : Representation ℂ (CircleTorusCharacterLattice.Torus d) E)
    (hDimension : Module.finrank ℂ E = 1)
    (hUnitary : IsUnitaryRepresentation rho)
    (hContinuous : IsJointlyContinuous rho) :
    ∃! weight : d → ℤ,
      continuousCircleCharacter rho hDimension hUnitary hContinuous =
        CircleTorusCharacterLattice.torusCharacter weight :=
  CircleTorusCharacterLattice.existsUnique_eq_torusCharacter
    (continuousCircleCharacter rho hDimension hUnitary hContinuous)

end FiniteTorus

end
end OneDimensionalUnitaryCharacter
end Math
