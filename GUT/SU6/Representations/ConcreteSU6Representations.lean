import GUT.SU6.Adapters.RepresentationExteriorEquiv
import GUT.SU6.Representations.ContinuousUnitaryConstructions

open Math

/-!
# Concrete continuous unitary SU(6) representations

The defining representation is placed on the Euclidean `L2` model of
`C^6`. Finite wedge-basis coordinates and Haar averaging give a continuous
unitary exterior square, algebraically equivalent to the existing certified
fifteen-dimensional representation. The dual defining representation is
constructed with the same analytic guarantees. Tensor and antisymmetric
subspace constructions are also provided.
-/

namespace GUT
namespace ConcreteSU6Representations

open CompactEmbeddingClassification
open ContinuousRepresentationScope
open ContinuousUnitaryConstructions
open ContinuousUnitaryWeightDecomposition
open FiniteBasisHilbertization
open scoped TensorProduct

noncomputable section

abbrev SU6 := ActualRestriction.SU6
abbrev E6 := CompactEmbeddingClassification.EuclideanRepSpace

/-- The defining matrix action on the Euclidean `L2` model of `C^6`. -/
def fundamentalRho : Representation ℂ SU6 E6 where
  toFun g := Matrix.toEuclideanLin
    (((g : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
  map_one' := by
    simp [Module.End.one_eq_id]
  map_mul' := by
    intro g h
    change
      Matrix.toEuclideanLin
          (((g : Matrix (Fin 6) (Fin 6) ℂ) *
            (h : Matrix (Fin 6) (Fin 6) ℂ))) =
        Matrix.toEuclideanLin
            (((g : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) *
          Matrix.toEuclideanLin
            (((h : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
    rw [Module.End.mul_eq_comp]
    exact Matrix.toLpLin_mul_same 2 _ _

/-- The Euclidean defining action preserves its standard Hermitian inner
product. -/
theorem fundamentalRho_unitary :
    IsUnitaryRepresentation fundamentalRho := by
  intro g x y
  apply unitaryMatrix_preserves_inner
  have hUnitary :
      (((g : SU6) : Matrix (Fin 6) (Fin 6) ℂ) :
          Matrix (Fin 6) (Fin 6) ℂ) ∈ Matrix.unitaryGroup (Fin 6) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup g.prop
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp hUnitary)

/-- The defining matrix action is jointly continuous. -/
theorem fundamentalRho_jointlyContinuous :
    IsJointlyContinuous fundamentalRho := by
  change Continuous fun p : SU6 × E6 =>
    WithLp.toLp 2
      (Matrix.mulVec
        (((p.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
        (WithLp.ofLp p.2))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 6 => ℂ)).comp
  exact
    (continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 (fun _ : Fin 6 => ℂ)).comp continuous_snd)

/-- The concrete continuous-unitary defining representation. -/
def fundamental : ContinuousUnitarySU6Representation where
  V := E6
  rho := fundamentalRho
  unitary := fundamentalRho_unitary
  continuous_action := fundamentalRho_jointlyContinuous

/-- Forgetting the Euclidean norm recovers the algebraic defining
representation used by the weight certificates. -/
def fundamentalEquiv :
    Representation.Equiv fundamental.rho FundamentalRepresentation.rho :=
  Representation.Equiv.mk (WithLp.linearEquiv 2 ℂ (Fin 6 → ℂ)) (by
    intro g
    apply LinearMap.ext
    intro x
    rfl)

/-- An analytic realization of the original algebraic defining action. -/
def fundamentalWitness :
    ContinuousUnitarizableWitness FundamentalRepresentation.actual where
  model := fundamental
  equiv := fundamentalEquiv.symm

/-- The continuous-unitary conjugate fundamental representation. -/
def antifundamental : ContinuousUnitarySU6Representation :=
  ContinuousUnitarySU6Representation.dual fundamental

/-- The analytic conjugate fundamental is the algebraic dual of `6`. -/
def antifundamentalEquiv :
    Representation.Equiv
      (CertifiedConstructions.dualActual FundamentalRepresentation.actual).rho
      antifundamental.rho :=
  (CertifiedConstructions.dualEquiv
    (R := FundamentalRepresentation.actual)
    (S := fundamental.toActualRepresentation) fundamentalEquiv.symm).trans
      (ContinuousUnitarySU6Representation.dualEquiv fundamental)

/-- The conjugate fundamental has complex dimension six. -/
theorem antifundamental_finrank : Module.finrank ℂ antifundamental.V = 6 := by
  rw [← antifundamentalEquiv.toLinearEquiv.finrank_eq]
  change Module.finrank ℂ (Module.Dual ℂ (Fin 6 → ℂ)) = 6
  rw [Subspace.dual_finrank_eq]
  simp

/-- The dual weight certificate and its analytic realization describe the
same actual representation. -/
def antifundamentalWitness :
    ContinuousUnitarizableWitness
      (CertifiedConstructions.dualActual FundamentalRepresentation.actual) where
  model := antifundamental
  equiv := antifundamentalEquiv

/-!
## The exterior-square model
-/

/-- The Euclidean defining action, forgetting its analytic structure. -/
def euclideanActual : VirtualRestriction.ActualSU6Representation where
  V := E6
  rho := fundamentalRho

/-- The standard algebraic basis of the Euclidean defining space. -/
def fundamentalBasis : Module.Basis (Fin 6) ℂ E6 :=
  (EuclideanSpace.basisFun (Fin 6) ℂ).toBasis

abbrev ExteriorTwoIndex := Set.powersetCard (Fin 6) 2

/-- The canonical wedge basis of the algebraic exterior square. -/
def exteriorTwoBasis :
    Module.Basis ExteriorTwoIndex ℂ
      (CertifiedConstructions.exteriorActual euclideanActual 2).V :=
  fundamentalBasis.exteriorPower 2

/-- A Euclidean coordinate copy of the algebraic exterior square. -/
abbrev ExteriorTwoSeedSpace := Copy exteriorTwoBasis

/-- The exterior-square action transported to its finite-basis Hilbert
copy. -/
def exteriorTwoSeedRho : Representation ℂ SU6 ExteriorTwoSeedSpace :=
  basisCopyRepresentation exteriorTwoBasis
    (CertifiedConstructions.exteriorActual euclideanActual 2).rho

/-- Every wedge-basis orbit has continuous coordinates: each coordinate is
a `2 x 2` minor of the defining matrix. -/
theorem exteriorTwo_basisOrbit_continuous (t : ExteriorTwoIndex) :
    Continuous fun g : SU6 =>
      (⟨(CertifiedConstructions.exteriorActual euclideanActual 2).rho g
          (exteriorTwoBasis t)⟩ : ExteriorTwoSeedSpace) := by
  rw [Copy.continuous_iff_coords]
  intro s
  let et := Set.powersetCard.ofFinEmbEquiv.symm t
  let es := Set.powersetCard.ofFinEmbEquiv.symm s
  have hCoordinate :
      (fun g : SU6 =>
        exteriorTwoBasis.coord s
          ((CertifiedConstructions.exteriorActual euclideanActual 2).rho g
            (exteriorTwoBasis t))) =
        fun g =>
          (Matrix.of fun i j : Fin 2 =>
            fundamentalBasis.coord (es j)
              (fundamentalRho g (fundamentalBasis (et i)))).det := by
    funext g
    change
      (fundamentalBasis.exteriorPower 2).coord s
          (exteriorPower.map 2 (fundamentalRho g)
            (fundamentalBasis.exteriorPower 2 t)) = _
    rw [exteriorPower.basis_coord, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family,
      exteriorPower.ιMulti_family,
      exteriorPower.ιMultiDual_apply_ιMulti]
    rfl
  rw [hCoordinate]
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact
    fundamentalBasis.coord (es j) |>.continuous_of_finiteDimensional.comp
      (fundamentalRho_jointlyContinuous.orbit (fundamentalBasis (et i)))

/-- Joint continuity of the exterior-square action on the seed Hilbert
copy. -/
theorem exteriorTwoSeedRho_jointlyContinuous :
    IsJointlyContinuous exteriorTwoSeedRho :=
  basisCopyRepresentation_jointlyContinuous exteriorTwoBasis
    (CertifiedConstructions.exteriorActual euclideanActual 2).rho
    exteriorTwo_basisOrbit_continuous

/-- The exterior-square seed is algebraically equivalent to the usual
exterior power. -/
def exteriorTwoSeedEquiv :
    Representation.Equiv
      (CertifiedConstructions.exteriorActual euclideanActual 2).rho
      exteriorTwoSeedRho :=
  basisCopyRepresentationEquiv exteriorTwoBasis
    (CertifiedConstructions.exteriorActual euclideanActual 2).rho

/-- Haar averaging over the full compact group gives the concrete
continuous-unitary exterior-square representation. -/
def exteriorTwo : ContinuousUnitarySU6Representation :=
  ContinuousSU6Unitarization.model exteriorTwoSeedRho
    exteriorTwoSeedRho_jointlyContinuous

/-- The continuous-unitary exterior square is representation-equivalent to
the algebraic exterior power and hence has exactly its character. -/
def exteriorTwoEquiv :
    Representation.Equiv
      (CertifiedConstructions.exteriorActual euclideanActual 2).rho
      exteriorTwo.rho :=
  exteriorTwoSeedEquiv.trans
    (ContinuousSU6Unitarization.modelEquiv exteriorTwoSeedRho
      exteriorTwoSeedRho_jointlyContinuous)

/-- The exterior-square model really has complex dimension fifteen. -/
theorem exteriorTwo_finrank : Module.finrank ℂ exteriorTwo.V = 15 := by
  rw [← exteriorTwoEquiv.toLinearEquiv.finrank_eq]
  change Module.finrank ℂ (⋀[ℂ]^2 E6) = 15
  rw [exteriorPower.finrank_eq]
  norm_num [E6, Nat.choose]

/-- The exterior square of the original algebraic defining representation
is equivalent to the continuous-unitary fifteen-dimensional model. -/
def exteriorTwoAlgebraicEquiv :
    Representation.Equiv
      (CertifiedConstructions.exteriorActual FundamentalRepresentation.actual 2).rho
      exteriorTwo.rho :=
  (CertifiedConstructions.exteriorEquiv
    (R := FundamentalRepresentation.actual) (S := euclideanActual)
    fundamentalEquiv.symm 2).trans exteriorTwoEquiv

/-- The algebraic `15` has an explicit continuous-unitary realization, so
its actual character has the faithful ambient Laurent model provided by hypercharge character rigidity. -/
def exteriorTwoWitness :
    ContinuousUnitarizableWitness
      (CertifiedConstructions.exteriorActual FundamentalRepresentation.actual 2) where
  model := exteriorTwo
  equiv := exteriorTwoAlgebraicEquiv

/-- Transport the previously checked wedge-weight certificate to the actual
analytic representation. -/
def exteriorTwoTorusEigenbasis :
    WeightTheory.TorusEigenbasis exteriorTwo.toActualRepresentation := by
  letI : LinearOrder FundamentalRepresentation.torusEigenbasis.ι :=
    inferInstanceAs (LinearOrder (Fin 6))
  exact CertifiedConstructions.TorusEigenbasis.equiv
    (CertifiedConstructions.TorusEigenbasis.exterior
      FundamentalRepresentation.torusEigenbasis 2)
    exteriorTwoAlgebraicEquiv

/-- Transport the dual-weight certificate to the analytic conjugate
fundamental representation. -/
def antifundamentalTorusEigenbasis :
    WeightTheory.TorusEigenbasis antifundamental.toActualRepresentation :=
  CertifiedConstructions.TorusEigenbasis.equiv
    (CertifiedConstructions.TorusEigenbasis.dual
      FundamentalRepresentation.torusEigenbasis)
    antifundamentalEquiv

/-- The continuous-unitary tensor square of the defining representation. -/
def tensorSquare : ContinuousUnitarySU6Representation :=
  ContinuousUnitarySU6Representation.tensor fundamental fundamental

/-- The antisymmetric tensors are the kernel of `swap + identity`. -/
def alternatingSquareSubmodule : Submodule ℂ (E6 ⊗[ℂ] E6) :=
  LinearMap.ker
    ((TensorProduct.comm ℂ E6 E6).toLinearMap + LinearMap.id)

@[simp]
theorem mem_alternatingSquareSubmodule_iff (z : E6 ⊗[ℂ] E6) :
    z ∈ alternatingSquareSubmodule ↔
      TensorProduct.comm ℂ E6 E6 z = -z := by
  rw [alternatingSquareSubmodule, LinearMap.mem_ker]
  simp only [LinearMap.add_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
    add_eq_zero_iff_eq_neg]

/-- Equal actions on both tensor factors commute with swap, so the
antisymmetric subspace is an `SU(6)` subrepresentation. -/
def alternatingSquareSubrepresentation :
    Subrepresentation (fundamentalRho.tprod fundamentalRho) where
  toSubmodule := alternatingSquareSubmodule
  apply_mem_toSubmodule g z hz := by
    rw [mem_alternatingSquareSubmodule_iff] at hz ⊢
    change
      TensorProduct.comm ℂ E6 E6
          (TensorProduct.map (fundamentalRho g) (fundamentalRho g) z) =
        -TensorProduct.map (fundamentalRho g) (fundamentalRho g) z
    rw [← TensorProduct.map_comm, hz, map_neg]

/-- The concrete continuous-unitary antisymmetric square. -/
def alternatingSquare : ContinuousUnitarySU6Representation where
  V := alternatingSquareSubrepresentation.toSubmodule
  rho := alternatingSquareSubrepresentation.toRepresentation
  unitary := by
    intro g x y
    exact
      (unitary_tprod fundamentalRho fundamentalRho
        fundamentalRho_unitary fundamentalRho_unitary) g x y
  continuous_action :=
    (jointlyContinuous_tprod fundamentalRho fundamentalRho
      fundamentalRho_jointlyContinuous fundamentalRho_jointlyContinuous).subrepresentation
      alternatingSquareSubrepresentation

end
end ConcreteSU6Representations
end GUT
