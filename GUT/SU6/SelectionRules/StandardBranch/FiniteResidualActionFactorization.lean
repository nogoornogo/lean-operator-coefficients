import GUT.SU6.SelectionRules.StandardBranch.FiniteAbelianChargeSectors
import GUT.SU6.Hypercharge.StandardCentralGauge

open Physics

open Math

/-!
# Factoring an Abelian residual action into gauge and commuting parts

An ordinary Abelian residual internal symmetry can be represented on a matter
source only up to an `SU(6)` gauge transformation.  This file isolates the exact
algebraic input needed for that statement.  A gauge-twisted action conjugates
the `SU(6)` representation by a specified lift into `SU(6)`.  Removing that
lift produces an honest action which commutes with the full gauge group.

For any Abelian residual group, unitarity and finite-dimensionality decompose
the commuting action into finitely many character sectors; finiteness of the
group is not needed.  The remaining physical input is the existence of the
gauge lift and the identification of its standard-branch central component
with the common central character used by charge resolution.
-/

namespace GUT
namespace FiniteResidualActionFactorization

open CompactEmbeddingClassification
open ContinuousUnitaryWeightDecomposition
open FiniteAbelianChargeSectors

noncomputable section

abbrev SU6 := ActualRestriction.SU6

/-- A physical action whose failure to commute with `SU(6)` is exactly an
inner gauge transformation. -/
structure GaugeTwistedAction
    (H : Type*) [CommGroup H]
    (R : ContinuousUnitarySU6Representation) where
  physical : Representation ℂ H R.V
  unitary : IsUnitaryRepresentation physical
  gauge : H →* SU6
  covariance : ∀ h g,
    physical h * R.rho g =
      R.rho (gauge h * g * (gauge h)⁻¹) * physical h

/-- Topological refinement of a gauge-twisted action.  Both the physical
action and its chosen gauge lift vary continuously with the residual-group
element. -/
structure ContinuousGaugeTwistedAction
    (H : Type*) [CommGroup H] [TopologicalSpace H]
    (R : ContinuousUnitarySU6Representation)
    extends GaugeTwistedAction H R where
  physical_continuous :
    ContinuousRepresentationScope.IsJointlyContinuous
      toGaugeTwistedAction.physical
  gauge_continuous : Continuous toGaugeTwistedAction.gauge

namespace GaugeTwistedAction

variable {H : Type*} [CommGroup H]
variable {R : ContinuousUnitarySU6Representation}

/-- A strict ordinary internal action, namely one commuting with the full
`SU(6)` gauge action, is a gauge-twisted action with the identity gauge lift.
This is the canonical specialization relevant to ordinary internal
symmetries; no choice of lift remains. -/
def ofCommuting (S : FiniteAbelianChargeSectors.CommutingAction H R) :
    GaugeTwistedAction H R where
  physical := S.rho
  unitary := S.unitary
  gauge := 1
  covariance := by
    intro h g
    simpa using S.commutes h g

@[simp]
theorem ofCommuting_gauge
    (S : FiniteAbelianChargeSectors.CommutingAction H R) :
    (ofCommuting S).gauge = (1 : H →* SU6) :=
  rfl

/-- The gauge lifts commute because their source group is Abelian. -/
theorem gauge_commute (T : GaugeTwistedAction H R) (h k : H) :
    Commute (T.gauge h) (T.gauge k) := by
  change T.gauge h * T.gauge k = T.gauge k * T.gauge h
  rw [← map_mul, mul_comm h k, map_mul]

/-- A physical residual transformation commutes with the inverse gauge lift
of every other residual transformation. -/
theorem physical_commutes_gauge_inv
    (T : GaugeTwistedAction H R) (h k : H) :
    T.physical h * R.rho (T.gauge k)⁻¹ =
      R.rho (T.gauge k)⁻¹ * T.physical h := by
  have hCov := T.covariance h (T.gauge k)⁻¹
  rw [(T.gauge_commute h k).inv_right.mul_inv_cancel] at hCov
  exact hCov

/-- Remove the chosen inner gauge transformation from the physical action. -/
def externalRepresentation (T : GaugeTwistedAction H R) :
    Representation ℂ H R.V where
  toFun h := R.rho (T.gauge h)⁻¹ * T.physical h
  map_one' := by simp
  map_mul' h k := by
    have hComm := T.gauge_commute h k
    have hMove := T.physical_commutes_gauge_inv h k
    change
      R.rho (T.gauge (h * k))⁻¹ * T.physical (h * k) =
        (R.rho (T.gauge h)⁻¹ * T.physical h) *
          (R.rho (T.gauge k)⁻¹ * T.physical k)
    rw [map_mul, hComm.mul_inv, map_mul, map_mul]
    calc
      (R.rho (T.gauge h)⁻¹ * R.rho (T.gauge k)⁻¹) *
          (T.physical h * T.physical k) =
        R.rho (T.gauge h)⁻¹ *
          ((R.rho (T.gauge k)⁻¹ * T.physical h) * T.physical k) := by
            simp only [mul_assoc]
      _ = R.rho (T.gauge h)⁻¹ *
          ((T.physical h * R.rho (T.gauge k)⁻¹) * T.physical k) := by
            rw [hMove]
      _ = (R.rho (T.gauge h)⁻¹ * T.physical h) *
          (R.rho (T.gauge k)⁻¹ * T.physical k) := by
            simp only [mul_assoc]

/-- Removing the identity gauge lift leaves the original ordinary internal
action unchanged. -/
theorem ofCommuting_externalRepresentation
    (S : FiniteAbelianChargeSectors.CommutingAction H R) :
    (ofCommuting S).externalRepresentation = S.rho := by
  ext h v
  simp [ofCommuting, externalRepresentation]

/-- After removing the inner gauge lift, the residual action commutes with
the full `SU(6)` representation. -/
theorem externalRepresentation_commutes
    (T : GaugeTwistedAction H R) (h : H) (g : SU6) :
    T.externalRepresentation h * R.rho g =
      R.rho g * T.externalRepresentation h := by
  change
    (R.rho (T.gauge h)⁻¹ * T.physical h) * R.rho g =
      R.rho g * (R.rho (T.gauge h)⁻¹ * T.physical h)
  calc
    (R.rho (T.gauge h)⁻¹ * T.physical h) * R.rho g =
        R.rho (T.gauge h)⁻¹ * (T.physical h * R.rho g) := by
          rw [mul_assoc]
    _ = R.rho (T.gauge h)⁻¹ *
        (R.rho (T.gauge h * g * (T.gauge h)⁻¹) * T.physical h) := by
          rw [T.covariance h g]
    _ = (R.rho (T.gauge h)⁻¹ *
          R.rho (T.gauge h * g * (T.gauge h)⁻¹)) * T.physical h := by
          rw [← mul_assoc]
    _ = R.rho ((T.gauge h)⁻¹ *
          (T.gauge h * g * (T.gauge h)⁻¹)) * T.physical h := by
          rw [← map_mul]
    _ = R.rho (g * (T.gauge h)⁻¹) * T.physical h := by
          simp [mul_assoc]
    _ = (R.rho g * R.rho (T.gauge h)⁻¹) * T.physical h := by
          rw [map_mul]
    _ = R.rho g * (R.rho (T.gauge h)⁻¹ * T.physical h) := by
          rw [mul_assoc]

/-- The external action remains unitary. -/
theorem externalRepresentation_unitary
    (T : GaugeTwistedAction H R) :
    IsUnitaryRepresentation T.externalRepresentation := by
  intro h v w
  change
    inner ℂ
        (R.rho (T.gauge h)⁻¹ (T.physical h v))
        (R.rho (T.gauge h)⁻¹ (T.physical h w)) =
      inner ℂ v w
  calc
    inner ℂ
        (R.rho (T.gauge h)⁻¹ (T.physical h v))
        (R.rho (T.gauge h)⁻¹ (T.physical h w)) =
      inner ℂ (T.physical h v) (T.physical h w) :=
        R.unitary (T.gauge h)⁻¹ (T.physical h v) (T.physical h w)
    _ = inner ℂ v w := T.unitary h v w

/-- Package the gauge-removed action for the Abelian-character sector theorem. -/
def externalCommutingAction (T : GaugeTwistedAction H R) :
    FiniteAbelianChargeSectors.CommutingAction H R where
  rho := T.externalRepresentation
  unitary := T.externalRepresentation_unitary
  commutes := T.externalRepresentation_commutes

/-- The original physical action is exactly gauge lift followed by the
commuting external action. -/
theorem gauge_mul_external_eq_physical
    (T : GaugeTwistedAction H R) (h : H) :
    R.rho (T.gauge h) * T.externalRepresentation h = T.physical h := by
  change
    R.rho (T.gauge h) *
        (R.rho (T.gauge h)⁻¹ * T.physical h) =
      T.physical h
  rw [← mul_assoc, ← map_mul]
  simp

theorem gauge_mul_external_apply
    (T : GaugeTwistedAction H R) (h : H) (v : R.V) :
    R.rho (T.gauge h) (T.externalRepresentation h v) =
      T.physical h v := by
  exact LinearMap.congr_fun (T.gauge_mul_external_eq_physical h) v

/-- The factorized Abelian residual action therefore has a finite collection
of full character sectors which independently span the source. -/
theorem exists_external_character_sector_cover
    (T : GaugeTwistedAction H R) :
    ∃ chars : Finset (H →* Circle),
      iSupIndep (fun chi : ↥chars =>
        T.externalCommutingAction.characterSubmodule chi.1) ∧
      (⨆ chi : ↥chars,
        T.externalCommutingAction.characterSubmodule chi.1) = ⊤ :=
  T.externalCommutingAction.exists_finite_character_sector_cover

/-- Once a common standard-branch central character is supplied, the
factorized Abelian residual action produces the chargewise Weyl-invariant standard charge-orbit bridge
source used by the ordinary Abelian obstruction. -/
theorem chargedSource_resolvedCharacter_isWeylInvariant
    (T : GaugeTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.externalRepresentation)
    (coeff : ℤ) (eta : H →* Circle) :
    StandardAbelianCharge.ResolvedWeylInvariant
      ((T.externalCommutingAction.chargedSectorSource D coeff).resolvedCharacter
        (centralDegreeCharge eta)) :=
  FiniteAbelianChargeSectors.CommutingAction.chargedSectorSource_resolvedCharacter_isWeylInvariant
    T.externalCommutingAction D coeff eta

end GaugeTwistedAction

namespace ContinuousGaugeTwistedAction

variable {H : Type*} [CommGroup H] [TopologicalSpace H]
variable {R : ContinuousUnitarySU6Representation}

/-- Inversion is continuous on the concrete matrix model of `SU(6)`.  The
ambient special-unitary subtype does not currently expose this instance
directly in mathlib. -/
theorem su6_inverse_continuous : Continuous fun g : SU6 => g⁻¹ := by
  apply continuous_induced_rng.mpr
  change Continuous fun g : SU6 =>
    star ((g : SU6) : Matrix (Fin 6) (Fin 6) ℂ)
  exact continuous_star.comp continuous_subtype_val

/-- A continuous physical action whose gauge lift is the standard central
circle automatically has a continuous gauge lift. -/
def ofStandardCentral
    (T : GaugeTwistedAction H R)
    (hPhysical : ContinuousRepresentationScope.IsJointlyContinuous T.physical)
    (eta : H →ₜ* Circle)
    (hGauge : T.gauge =
      StandardCentralGauge.hom.comp (eta : H →* Circle)) :
    ContinuousGaugeTwistedAction H R where
  toGaugeTwistedAction := T
  physical_continuous := hPhysical
  gauge_continuous := by
    rw [hGauge]
    exact StandardCentralGauge.hom_continuous.comp eta.continuous

/-- Removing a continuously varying inner gauge lift preserves joint
continuity of the residual action. -/
theorem externalRepresentation_jointlyContinuous
    (T : ContinuousGaugeTwistedAction H R) :
    ContinuousRepresentationScope.IsJointlyContinuous
      T.toGaugeTwistedAction.externalRepresentation := by
  change Continuous fun p : H × R.V =>
    R.rho (T.toGaugeTwistedAction.gauge p.1)⁻¹
      (T.toGaugeTwistedAction.physical p.1 p.2)
  exact Continuous.comp R.continuous_action
    ((su6_inverse_continuous.comp
        (T.gauge_continuous.comp continuous_fst)).prodMk
      T.physical_continuous)

/-- The character of every simple block in the gauge-removed action is a
continuous circle-valued character. -/
def continuousBlockCharacter
    (T : ContinuousGaugeTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin D.numberOfBlocks) : H →ₜ* Circle := by
  letI : FiniteDimensional ℂ
      (T.toGaugeTwistedAction.externalCommutingAction.Block D i) :=
    T.toGaugeTwistedAction.externalCommutingAction.blockFiniteDimensional D i
  exact OneDimensionalUnitaryCharacter.continuousCircleCharacter
    (D.subrepresentation i).toRepresentation
    (T.toGaugeTwistedAction.externalCommutingAction.block_finrank_eq_one D i)
    (T.toGaugeTwistedAction.externalCommutingAction.blockRepresentation_unitary D i)
    (T.externalRepresentation_jointlyContinuous.subrepresentation
      (D.subrepresentation i))

/-- Forgetting continuity recovers exactly the block character used by the
algebraic sector decomposition. -/
theorem continuousBlockCharacter_toMonoidHom
    (T : ContinuousGaugeTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin D.numberOfBlocks) :
    (T.continuousBlockCharacter D i : H →* Circle) =
      T.toGaugeTwistedAction.externalCommutingAction.blockCharacter D i := by
  rfl

/-- Every character selected by the finite active-sector enumeration is
continuous when the original residual action and gauge lift are continuous. -/
theorem indexedCharacter_continuous
    (T : ContinuousGaugeTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin
      (T.toGaugeTwistedAction.externalCommutingAction.NumberOfActiveCharacters D)) :
    Continuous
      (T.toGaugeTwistedAction.externalCommutingAction.indexedCharacter D i) := by
  classical
  let S := T.toGaugeTwistedAction.externalCommutingAction
  let chi : ↥(S.activeCharacters D) := S.activeCharacterEquiv D i
  obtain ⟨j, _hj, hCharacter⟩ :=
    Finset.mem_image.mp chi.property
  have hContinuous : Continuous (S.blockCharacter D j) := by
    rw [← T.continuousBlockCharacter_toMonoidHom D j]
    exact (T.continuousBlockCharacter D j).continuous
  change Continuous (S.indexedCharacter D i)
  rw [show S.indexedCharacter D i = chi.1 from rfl, ← hCharacter]
  exact hContinuous

/-- Bundle an enumerated external-sector label as a continuous character. -/
def continuousIndexedCharacter
    (T : ContinuousGaugeTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin
      (T.toGaugeTwistedAction.externalCommutingAction.NumberOfActiveCharacters D)) :
    H →ₜ* Circle where
  toMonoidHom :=
    T.toGaugeTwistedAction.externalCommutingAction.indexedCharacter D i
  continuous_toFun := T.indexedCharacter_continuous D i

/-- For a continuous residual circle, every external charge sector has a
unique integer charge. -/
theorem existsUnique_indexedIntegerCharge
    {R : ContinuousUnitarySU6Representation}
    (T : ContinuousGaugeTwistedAction Circle R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin
      (T.toGaugeTwistedAction.externalCommutingAction.NumberOfActiveCharacters D)) :
    ∃! n : ℤ, T.continuousIndexedCharacter D i =
      CircleHomLattice.circlePowerHom n :=
  CircleHomLattice.existsUnique_eq_circlePowerHom
    (T.continuousIndexedCharacter D i)

end ContinuousGaugeTwistedAction

/-!
## Specialization to the standard central gauge circle
-/

/-- A gauge-twisted action whose inner gauge lift is explicitly the common
central circle of the standard `U(5)` branch.  This is a precise certificate,
not an assertion that every physical residual action has such a lift. -/
structure StandardCentralTwistedAction
    (H : Type*) [CommGroup H]
    (R : ContinuousUnitarySU6Representation)
    extends GaugeTwistedAction H R where
  centralCharacter : H →* Circle
  gauge_eq : toGaugeTwistedAction.gauge =
    StandardCentralGauge.hom.comp centralCharacter

namespace StandardCentralTwistedAction

variable {H : Type*} [CommGroup H]
variable {R : ContinuousUnitarySU6Representation}

theorem gauge_apply
    (T : StandardCentralTwistedAction H R) (h : H) :
    T.toGaugeTwistedAction.gauge h =
      StandardCentralGauge.hom (T.centralCharacter h) := by
  have hAt := congrArg
    (fun f : H →* SU6 => f h) T.gauge_eq
  exact hAt

/-- The concrete central gauge point followed by the gauge-removed action is
the original physical residual action. -/
theorem centralGauge_mul_external_eq_physical
    (T : StandardCentralTwistedAction H R) (h : H) :
    R.rho (StandardCentralGauge.hom (T.centralCharacter h)) *
        T.toGaugeTwistedAction.externalRepresentation h =
      T.toGaugeTwistedAction.physical h := by
  rw [← T.gauge_apply h]
  exact T.toGaugeTwistedAction.gauge_mul_external_eq_physical h

/-- The same factorization using the checked diagonal realization of the
standard central circle. -/
theorem diagonalGauge_mul_external_eq_physical
    (T : StandardCentralTwistedAction H R) (h : H) :
    R.rho (StandardCentralGauge.diagonalPoint
        (T.centralCharacter h)).toSU6 *
        T.toGaugeTwistedAction.externalRepresentation h =
      T.toGaugeTwistedAction.physical h := by
  rw [StandardCentralGauge.diagonalPoint_toSU6_eq_hom]
  exact T.centralGauge_mul_external_eq_physical h

/-- The multiplicative phase of the central gauge lift on a Laurent monomial
is exactly evaluation of the additive `centralDegreeCharge` used by standard charge-orbit bridge. -/
theorem laurentCentralPhase_eq_chargeEvaluation
    (T : StandardCentralTwistedAction H R)
    (e : AmbientWeightLattice.Exponent) (h : H) :
    AmbientLaurent.Exponent.eval e
        (StandardCentralGauge.torusVec (T.centralCharacter h)) =
      (((centralDegreeCharge T.centralCharacter
        (StandardAbelianCharge.totalDegree e)).toMul h : Circle) : ℂ) := by
  rw [StandardCentralGauge.exponent_eval_torusVec]
  rfl

/-- On a vector carrying external character `chi` and central Laurent weight
`e`, the original physical residual action has exactly the affine charge used
by standard charge-orbit bridge. -/
theorem physical_action_on_affineEigenvector
    (T : StandardCentralTwistedAction H R)
    (chi : H →* Circle) (e : AmbientWeightLattice.Exponent) (v : R.V)
    (hExternal : ∀ h,
      T.toGaugeTwistedAction.externalRepresentation h v =
        ((chi h : Circle) : ℂ) • v)
    (hCentral : ∀ z : Circle,
      R.rho (StandardCentralGauge.hom z) v =
        AmbientLaurent.Exponent.eval e
          (StandardCentralGauge.torusVec z) • v)
    (h : H) :
    T.toGaugeTwistedAction.physical h v =
      ((((Additive.ofMul chi + centralDegreeCharge T.centralCharacter
        (StandardAbelianCharge.totalDegree e)).toMul h : Circle) : ℂ)) • v := by
  have hFactor := congrArg
    (fun f : Module.End ℂ R.V => f v)
    (T.centralGauge_mul_external_eq_physical h)
  calc
    T.toGaugeTwistedAction.physical h v =
        R.rho (StandardCentralGauge.hom (T.centralCharacter h))
          (T.toGaugeTwistedAction.externalRepresentation h v) := hFactor.symm
    _ = R.rho (StandardCentralGauge.hom (T.centralCharacter h))
          (((chi h : Circle) : ℂ) • v) := by rw [hExternal h]
    _ = ((chi h : Circle) : ℂ) •
        R.rho (StandardCentralGauge.hom (T.centralCharacter h)) v := by
          rw [map_smul]
    _ = ((chi h : Circle) : ℂ) •
        (AmbientLaurent.Exponent.eval e
          (StandardCentralGauge.torusVec (T.centralCharacter h)) • v) := by
          rw [hCentral]
    _ = ((((Additive.ofMul chi + centralDegreeCharge T.centralCharacter
          (StandardAbelianCharge.totalDegree e)).toMul h : Circle) : ℂ)) • v := by
          rw [smul_smul, T.laurentCentralPhase_eq_chargeEvaluation e h]
          rfl

/-- The canonical integral torus-weight basis of one full external character
sector.  Its Laurent polynomial is the one used by that sector's hypercharge character rigidity model. -/
def indexedSectorWeightBasis
    (T : StandardCentralTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin
      (T.toGaugeTwistedAction.externalCommutingAction.NumberOfActiveCharacters D)) :
    ContinuousUnitaryWeightDecomposition.IntegerWeightBasis
      (T.toGaugeTwistedAction.externalCommutingAction.characterSector
        (T.toGaugeTwistedAction.externalCommutingAction.indexedCharacter D i)).rho := by
  let Q := T.toGaugeTwistedAction.externalCommutingAction.characterSector
    (T.toGaugeTwistedAction.externalCommutingAction.indexedCharacter D i)
  exact ContinuousUnitaryWeightDecomposition.integerWeightBasisOfContinuousUnitary
    Q.rho Q.unitary Q.continuous_action

/-- The basis used in the affine physical-action theorem is definitionally
the basis whose normalized `Finsupp` polynomial realizes the sector's actual
restricted trace character. -/
theorem indexedSectorWeightBasis_poly_eq_ambientLaurentModel
    (T : StandardCentralTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin
      (T.toGaugeTwistedAction.externalCommutingAction.NumberOfActiveCharacters D)) :
    (T.indexedSectorWeightBasis D i).poly =
      (T.toGaugeTwistedAction.externalCommutingAction.characterSector
        (T.toGaugeTwistedAction.externalCommutingAction.indexedCharacter D i)).ambientLaurentModel.poly := by
  rfl

/-- Every basis vector underlying the actual Laurent model of a character
sector carries the corresponding affine physical residual charge. -/
theorem physical_action_on_indexedSectorWeightBasis
    (T : StandardCentralTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (i : Fin
      (T.toGaugeTwistedAction.externalCommutingAction.NumberOfActiveCharacters D))
    (j : (T.indexedSectorWeightBasis D i).ι) (h : H) :
    T.toGaugeTwistedAction.physical h
        ((T.indexedSectorWeightBasis D i).basis j).1 =
      (((Additive.ofMul
          (T.toGaugeTwistedAction.externalCommutingAction.indexedCharacter D i) +
        centralDegreeCharge T.centralCharacter
          (StandardAbelianCharge.totalDegree
            ((T.indexedSectorWeightBasis D i).weight j))).toMul h : Circle) : ℂ) •
        ((T.indexedSectorWeightBasis D i).basis j).1 := by
  let S := T.toGaugeTwistedAction.externalCommutingAction
  let chi := S.indexedCharacter D i
  let B := T.indexedSectorWeightBasis D i
  apply T.physical_action_on_affineEigenvector chi (B.weight j) (B.basis j).1
  · intro k
    exact (B.basis j).property k
  · intro z
    let x := AmbientTorus.ofDiagonalPoint
      (StandardCentralGauge.diagonalPoint z)
    have hBasis := B.action_on_basis x j
    have hBasisAmbient := congrArg Subtype.val hBasis
    have hGroup : AmbientTorus.toSU6 x = StandardCentralGauge.hom z := by
      calc
        AmbientTorus.toSU6 x =
            (StandardCentralGauge.diagonalPoint z).toSU6 := by
          exact congrArg ActualRestriction.DiagonalSU6Point.toSU6
            (AmbientTorus.diagonalPoint_ofDiagonalPoint
              (StandardCentralGauge.diagonalPoint z))
        _ = StandardCentralGauge.hom z :=
          StandardCentralGauge.diagonalPoint_toSU6_eq_hom z
    rw [hGroup] at hBasisAmbient
    exact hBasisAmbient

/-- A certified standard-central Abelian residual action supplies exactly the
chargewise Weyl-invariant affine source used in the standard charge-orbit bridge route. -/
theorem chargedSource_resolvedCharacter_isWeylInvariant
    (T : StandardCentralTwistedAction H R)
    (D : FiniteSemisimpleDecomposition.Decomposition
      T.toGaugeTwistedAction.externalRepresentation)
    (coeff : ℤ) :
    StandardAbelianCharge.ResolvedWeylInvariant
      ((T.toGaugeTwistedAction.externalCommutingAction.chargedSectorSource
          D coeff).resolvedCharacter
        (centralDegreeCharge T.centralCharacter)) :=
  GaugeTwistedAction.chargedSource_resolvedCharacter_isWeylInvariant
    T.toGaugeTwistedAction D coeff T.centralCharacter

end StandardCentralTwistedAction

/-!
## Finite-dimensional physical-source certificates
-/

/-- One actual continuous-unitary `SU(6)` matter summand carrying a physical
Abelian residual action with the specified common central gauge character. -/
structure StandardCentralSummand
    (H : Type*) [CommGroup H] (eta : H →* Circle) where
  coeff : ℤ
  rep : ContinuousUnitarySU6Representation
  twisted : GaugeTwistedAction H rep
  gauge_eq : twisted.gauge = StandardCentralGauge.hom.comp eta

namespace StandardCentralSummand

variable {H : Type*} [CommGroup H]
variable {eta : H →* Circle}

def certifiedAction (s : StandardCentralSummand H eta) :
    StandardCentralTwistedAction H s.rep where
  toGaugeTwistedAction := s.twisted
  centralCharacter := eta
  gauge_eq := s.gauge_eq

/-- Unitary decomposition of the gauge-removed Abelian action. -/
def decomposition (s : StandardCentralSummand H eta) :
    FiniteSemisimpleDecomposition.Decomposition
      s.twisted.externalRepresentation :=
  Classical.choice (FiniteSemisimpleDecomposition.exists_decomposition
    s.twisted.externalRepresentation
    s.twisted.externalCommutingAction.isSemisimpleRepresentation)

/-- Convert one certified physical summand into all of its full external
character sectors, preserving the original virtual coefficient. -/
def toChargedSource (s : StandardCentralSummand H eta) :
    StandardPhysicalSource.FiniteChargedContinuousUnitarySource
      (ChargeLabel H) :=
  s.twisted.externalCommutingAction.chargedSectorSource
    s.decomposition s.coeff

theorem toChargedSource_resolvedCharacter_isWeylInvariant
    (s : StandardCentralSummand H eta) :
    StandardAbelianCharge.ResolvedWeylInvariant
      (s.toChargedSource.resolvedCharacter
        (centralDegreeCharge eta)) :=
  s.twisted.externalCommutingAction
    |>.chargedSectorSource_resolvedCharacter_isWeylInvariant
      s.decomposition s.coeff eta

/-- The sector decomposition used by the charged source recovers the original
`SU(6)` representation exactly. -/
def sectorRepresentationEquiv
    (s : StandardCentralSummand H eta) :
    Representation.Equiv
      (s.twisted.externalCommutingAction.sectorDirectSumRepresentation
        s.decomposition)
      s.rep.rho :=
  s.twisted.externalCommutingAction.sectorRepresentationEquiv s.decomposition

end StandardCentralSummand

/-!
## Continuous Abelian source certificates
-/

/-- One physical summand for a topological Abelian residual group.  The
physical action and the gauge lift are jointly/pointwise continuous, and the
common standard-central component is supplied as a continuous character. -/
structure ContinuousStandardCentralSummand
    (H : Type*) [CommGroup H] [TopologicalSpace H]
    (eta : H →ₜ* Circle) where
  coeff : ℤ
  rep : ContinuousUnitarySU6Representation
  twisted : GaugeTwistedAction H rep
  physical_continuous :
    ContinuousRepresentationScope.IsJointlyContinuous twisted.physical
  gauge_eq : twisted.gauge =
    StandardCentralGauge.hom.comp (eta : H →* Circle)

namespace ContinuousStandardCentralSummand

variable {H : Type*} [CommGroup H] [TopologicalSpace H]
variable {eta : H →ₜ* Circle}

/-- The continuous gauge-twisted action derived from the physical action,
the continuous central character, and the concrete standard gauge circle. -/
def continuousTwisted (s : ContinuousStandardCentralSummand H eta) :
    ContinuousGaugeTwistedAction H s.rep :=
  ContinuousGaugeTwistedAction.ofStandardCentral
    s.twisted s.physical_continuous eta s.gauge_eq

/-- Forget only the continuity witnesses, retaining the exact physical
factorization certificate used by the algebraic standard charge-orbit bridge argument. -/
def toStandardCentralSummand
    (s : ContinuousStandardCentralSummand H eta) :
    StandardCentralSummand H (eta : H →* Circle) where
  coeff := s.coeff
  rep := s.rep
  twisted := s.twisted
  gauge_eq := s.gauge_eq

/-- Every external charge sector produced from a continuous physical action
is labelled by a continuous character of the residual group. -/
theorem indexedCharacter_continuous
    (s : ContinuousStandardCentralSummand H eta)
    (i : Fin
      (s.twisted.externalCommutingAction.NumberOfActiveCharacters
        s.toStandardCentralSummand.decomposition)) :
    Continuous
      (s.twisted.externalCommutingAction.indexedCharacter
        s.toStandardCentralSummand.decomposition i) :=
  s.continuousTwisted.indexedCharacter_continuous
    s.toStandardCentralSummand.decomposition i

end ContinuousStandardCentralSummand

/-- A finite collection of certified matter summands sharing one standard
central residual character. -/
abbrev StandardCentralSource
    (H : Type*) [CommGroup H] (eta : H →* Circle) :=
  List (StandardCentralSummand H eta)

namespace StandardCentralSource

variable {H : Type*} [CommGroup H]
variable {eta : H →* Circle}

/-- Collect every full character sector of every physical summand. -/
def toChargedSource : StandardCentralSource H eta →
    StandardPhysicalSource.FiniteChargedContinuousUnitarySource
      (ChargeLabel H)
  | [] => []
  | s :: source => s.toChargedSource ++ toChargedSource source

/-- The source constructed from gauge-twisted Abelian actions is
chargewise Weyl invariant under the common central character. -/
theorem resolvedCharacter_isWeylInvariant
    (source : StandardCentralSource H eta) :
    StandardAbelianCharge.ResolvedWeylInvariant
      (source.toChargedSource.resolvedCharacter
        (centralDegreeCharge eta)) :=
  source.toChargedSource.resolvedCharacter_isWeylInvariant
    (centralDegreeCharge eta)

end StandardCentralSource

/-- A finite collection of continuous physical summands sharing one
continuous standard-central residual character. -/
abbrev ContinuousStandardCentralSource
    (H : Type*) [CommGroup H] [TopologicalSpace H]
    (eta : H →ₜ* Circle) :=
  List (ContinuousStandardCentralSummand H eta)

namespace ContinuousStandardCentralSource

variable {H : Type*} [CommGroup H] [TopologicalSpace H]
variable {eta : H →ₜ* Circle}

def toStandardCentralSource : ContinuousStandardCentralSource H eta →
    StandardCentralSource H (eta : H →* Circle)
  | [] => []
  | s :: source =>
      s.toStandardCentralSummand :: toStandardCentralSource source

def toChargedSource (source : ContinuousStandardCentralSource H eta) :
    StandardPhysicalSource.FiniteChargedContinuousUnitarySource
      (ChargeLabel H) :=
  source.toStandardCentralSource.toChargedSource

/-- Continuous physical source actions therefore produce a chargewise
Weyl-invariant standard charge-orbit bridge source, without using a continuous-anomaly equation. -/
theorem resolvedCharacter_isWeylInvariant
    (source : ContinuousStandardCentralSource H eta) :
    StandardAbelianCharge.ResolvedWeylInvariant
      (source.toChargedSource.resolvedCharacter
        (centralDegreeCharge (eta : H →* Circle))) :=
  source.toStandardCentralSource.resolvedCharacter_isWeylInvariant

end ContinuousStandardCentralSource

/-- The exact standard-branch Abelian-residual source hypothesis, with every
representation-theoretic component made explicit.  The remaining `spectrum`
field is the physical charge-resolved low-energy chiral-spectrum input. -/
structure PureSMAbelianResidualSource
    (H : Type*) [CommGroup H] where
  centralCharacter : H →* Circle
  matter : StandardCentralSource H centralCharacter
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges (ChargeLabel H)
  spectrum : StandardAbelianCharge.IsPureSMChargeSpectrum
    (matter.toChargedSource.resolvedCharacter
      (centralDegreeCharge centralCharacter))
    generations charges

namespace PureSMAbelianResidualSource

variable {H : Type*} [CommGroup H]

/-- Forget the action certificates after they have constructed the checked standard charge-orbit bridge
charged source. -/
def toPureSMChargedSource (S : PureSMAbelianResidualSource H) :
    StandardPhysicalSource.PureSMChargedSource (ChargeLabel H) where
  matter := S.matter.toChargedSource
  centralCharge := centralDegreeCharge S.centralCharacter
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  spectrum := S.spectrum

/-- Main Abelian standard-branch obstruction at character level.  It
uses standard charge-orbit bridge followed by Abelian proton-operator neutrality and no anomaly equation. -/
theorem protonCharacters_eq_one (S : PureSMAbelianResidualSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  residual_protonCharacters_eq_one S.toPureSMChargedSource

/-- Pointwise residual-group selection-rule form of the same obstruction. -/
theorem protonPhases_eq_one
    (S : PureSMAbelianResidualSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  residual_protonPhases_eq_one S.toPureSMChargedSource h

end PureSMAbelianResidualSource

/-- Continuous ordinary-Abelian specialization of the physical standard charge-orbit bridge source
hypothesis.  This route is independent of the auxiliary continuous-`U(1)`
anomaly identities. -/
structure PureSMContinuousAbelianResidualSource
    (H : Type*) [CommGroup H] [TopologicalSpace H] where
  centralCharacter : H →ₜ* Circle
  matter : ContinuousStandardCentralSource H centralCharacter
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : StandardBranchProtonObstruction.Charges (ChargeLabel H)
  spectrum : StandardAbelianCharge.IsPureSMChargeSpectrum
    (matter.toChargedSource.resolvedCharacter
      (centralDegreeCharge (centralCharacter : H →* Circle)))
    generations charges

namespace PureSMContinuousAbelianResidualSource

variable {H : Type*} [CommGroup H] [TopologicalSpace H]

/-- Forgetting continuity witnesses embeds the continuous physical source in
the general Abelian standard charge-orbit bridge certificate. -/
def toAbelianResidualSource
    (S : PureSMContinuousAbelianResidualSource H) :
    PureSMAbelianResidualSource H where
  centralCharacter := (S.centralCharacter : H →* Circle)
  matter := S.matter.toStandardCentralSource
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.charges
  spectrum := S.spectrum

/-- Continuous-Abelian standard charge-orbit bridge-to-Abelian proton-operator neutrality obstruction at character level, with no
anomaly premise. -/
theorem protonCharacters_eq_one
    (S : PureSMContinuousAbelianResidualSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  S.toAbelianResidualSource.protonCharacters_eq_one

/-- Pointwise selection-rule form for every element of the continuous
residual group. -/
theorem protonPhases_eq_one
    (S : PureSMContinuousAbelianResidualSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  S.toAbelianResidualSource.protonPhases_eq_one h

end PureSMContinuousAbelianResidualSource

/-- Explicit finite-Abelian specialization of the general residual-source
certificate. -/
abbrev PureSMFiniteResidualSource
    (H : Type*) [CommGroup H] [Finite H] :=
  PureSMAbelianResidualSource H

namespace PureSMFiniteResidualSource

variable {H : Type*} [CommGroup H] [Finite H]

/-- Finite-Abelian form of the standard charge-orbit bridge-to-Abelian proton-operator neutrality character obstruction. -/
theorem protonCharacters_eq_one (S : PureSMFiniteResidualSource H) :
    protonFirstCharacter S.charges = 1 ∧
      protonSecondCharacter S.charges = 1 :=
  PureSMAbelianResidualSource.protonCharacters_eq_one S

/-- Pointwise finite-group selection-rule form of the same obstruction. -/
theorem protonPhases_eq_one
    (S : PureSMFiniteResidualSource H) (h : H) :
    protonFirstCharacter S.charges h = 1 ∧
      protonSecondCharacter S.charges h = 1 :=
  PureSMAbelianResidualSource.protonPhases_eq_one S h

end PureSMFiniteResidualSource

end
end FiniteResidualActionFactorization
end GUT
