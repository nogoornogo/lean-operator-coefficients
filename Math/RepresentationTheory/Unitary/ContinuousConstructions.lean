import Math.RepresentationTheory.Unitary.ContinuousAction
import Math.RepresentationTheory.Unitary.UnitaryRepresentation
import Math.LinearAlgebra.FiniteBasisHilbertization
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Continuous unitary representations: basis copies and tensor products -/

namespace Math.ContinuousUnitaryConstructions
open CompactEmbeddingClassification ContinuousRepresentationScope FiniteBasisHilbertization
open scoped TensorProduct BigOperators
noncomputable section
universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {V : Type v} {W : Type w}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [FiniteDimensional ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable [FiniteDimensional ℂ W]

/-- In finite dimension, continuity of all representation orbits implies
joint continuity of the action. -/
theorem jointlyContinuous_of_orbit
    (rho : Representation ℂ G V)
    (hOrbit : ∀ v, Continuous fun g => rho g v) :
    IsJointlyContinuous rho := by
  let b := Module.finBasis ℂ V
  have hAction :
      (fun p : G × V => rho p.1 p.2) =
        fun p => ∑ i, (b.repr p.2 i) • rho p.1 (b i) := by
    funext p
    conv_lhs => rw [← b.sum_repr p.2]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_smul]
  rw [IsJointlyContinuous, hAction]
  apply continuous_finsetSum
  intro i _hi
  exact
    ((b.coord i).continuous_of_finiteDimensional.comp continuous_snd).smul
      ((hOrbit (b i)).comp continuous_fst)

/-!
## Analytic copies of algebraic representations
-/

variable {A : Type*} [AddCommGroup A] [Module ℂ A]
variable {ι : Type*} [Fintype ι]

/-- Transport an algebraic representation to the Hilbert copy determined by
a finite basis. -/
def basisCopyRepresentation
    (b : Module.Basis ι ℂ A) (rho : Representation ℂ G A) :
    Representation ℂ G (Copy b) where
  toFun g := (Copy.valLinearEquiv b).symm.toLinearMap.comp
    ((rho g).comp (Copy.valLinearEquiv b).toLinearMap)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

omit [TopologicalSpace G] [Fintype ι] in
@[simp]
theorem basisCopyRepresentation_apply
    (b : Module.Basis ι ℂ A) (rho : Representation ℂ G A)
    (g : G) (x : Copy b) :
    basisCopyRepresentation b rho g x = ⟨rho g x.val⟩ :=
  rfl

/-- The copied representation is algebraically equivalent to the original
one. -/
def basisCopyRepresentationEquiv
    (b : Module.Basis ι ℂ A) (rho : Representation ℂ G A) :
    Representation.Equiv rho (basisCopyRepresentation b rho) :=
  Representation.Equiv.mk (Copy.valLinearEquiv b).symm (by
    intro g
    ext x
    rfl)

/-- It is enough to check continuity of the finitely many copied basis
orbits. -/
theorem basisCopyRepresentation_jointlyContinuous
    (b : Module.Basis ι ℂ A) (rho : Representation ℂ G A)
    (hBasisOrbit : ∀ i, Continuous fun g =>
      (⟨rho g (b i)⟩ : Copy b)) :
    IsJointlyContinuous (basisCopyRepresentation b rho) := by
  apply jointlyContinuous_of_orbit
  intro x
  have hOrbitFormula :
      (fun g => basisCopyRepresentation b rho g x) =
        fun g => ∑ i, (b.repr x.val i) •
          (⟨rho g (b i)⟩ : Copy b) := by
    funext g
    apply (Copy.valLinearEquiv b).injective
    simp only [basisCopyRepresentation_apply, Copy.valLinearEquiv_apply,
      map_sum, map_smul]
    conv_lhs => rw [← b.sum_repr x.val]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_smul]
  rw [hOrbitFormula]
  apply continuous_finsetSum
  intro i _hi
  have hCoeff : Continuous (fun _ : G => (b.repr x.val i : ℂ)) :=
    continuous_const
  exact hCoeff.smul (hBasisOrbit i)

/-- Tensor products of finite-dimensional jointly continuous actions remain
jointly continuous. -/
theorem jointlyContinuous_tprod
    (rho : Representation ℂ G V)
    (sigma : Representation ℂ G W)
    (hRho : IsJointlyContinuous rho)
    (hSigma : IsJointlyContinuous sigma) :
    IsJointlyContinuous (rho.tprod sigma) := by
  apply jointlyContinuous_of_orbit
  let bV := Module.finBasis ℂ V
  let bW := Module.finBasis ℂ W
  let b := bV.tensorProduct bW
  intro z
  have hOrbitFormula :
      (fun g => (rho.tprod sigma) g z) =
        fun g => ∑ ij,
          (b.repr z ij) •
            (rho g (bV ij.1) ⊗ₜ[ℂ] sigma g (bW ij.2)) := by
    funext g
    conv_lhs => rw [← b.sum_repr z]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro ij _hij
    rw [map_smul]
    change
      (b.repr z ij) •
          TensorProduct.map (rho g) (sigma g) (b ij) =
        (b.repr z ij) •
          (rho g (bV ij.1) ⊗ₜ[ℂ] sigma g (bW ij.2))
    rw [show b ij = bV ij.1 ⊗ₜ[ℂ] bW ij.2 by
      exact Module.Basis.tensorProduct_apply bV bW ij.1 ij.2,
      TensorProduct.map_tmul]
  rw [hOrbitFormula]
  apply continuous_finsetSum
  intro ij _hij
  exact TensorProduct.continuous_tmul.comp
    ((continuous_const.smul (hRho.orbit (bV ij.1))).prodMk
      (hSigma.orbit (bW ij.2)))

/-- The action of one element of a unitary representation as a linear
isometry. -/
def actionIsometry
    (rho : Representation ℂ G V)
    (hUnitary : IsUnitaryRepresentation rho) (g : G) :
    V →ₗᵢ[ℂ] V :=
  (rho g).isometryOfInner (hUnitary g)

omit [TopologicalSpace G] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
/-- Tensor products of unitary representations remain unitary for the
canonical Hilbert tensor-product inner product. -/
theorem unitary_tprod
    (rho : Representation ℂ G V)
    (sigma : Representation ℂ G W)
    (hRho : IsUnitaryRepresentation rho)
    (hSigma : IsUnitaryRepresentation sigma) :
    IsUnitaryRepresentation (rho.tprod sigma) := by
  intro g x y
  change
    inner ℂ
        (TensorProduct.map
          (actionIsometry rho hRho g).toLinearMap
          (actionIsometry sigma hSigma g).toLinearMap x)
        (TensorProduct.map
          (actionIsometry rho hRho g).toLinearMap
          (actionIsometry sigma hSigma g).toLinearMap y) =
      inner ℂ x y
  exact TensorProduct.inner_map_map
    (actionIsometry rho hRho g) (actionIsometry sigma hSigma g) x y

end
end Math.ContinuousUnitaryConstructions
