import GUT.SU6.Embeddings.CompactEmbeddingClassification
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Continuous circles in the scalar centralizer

For an irreducible defining restriction, Schur's lemma forces every commuting
matrix to be scalar.  Inside `SU(6)` its scalar coefficient is a sixth root of
unity.  A continuous map from the connected circle to this finite set is
constant, so a commuting continuous hypercharge circle must be trivial.
-/

namespace GUT
namespace ContinuousCentralizer

open CompactEmbeddingClassification
open Polynomial

noncomputable section

/-- The action of one point of a commuting circle, regarded as an endomorphism
of the restricted defining representation. -/
def commutingCircleIntertwiner
    (iota : ProductGroup →* SU6) (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z) (z : Circle) :
    Representation.IntertwiningMap
      (definingRestriction iota) (definingRestriction iota) where
  toLinearMap := FundamentalRepresentation.rho (Y z)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    change
      FundamentalRepresentation.rho (Y z)
          (FundamentalRepresentation.rho (iota g) v) =
        FundamentalRepresentation.rho (iota g)
          (FundamentalRepresentation.rho (Y z) v)
    rw [← Module.End.mul_apply, ← map_mul, hCommute z g, map_mul,
      Module.End.mul_apply]

/-- The scalar coefficient is read from the first diagonal entry. -/
def scalarCoefficient (Y : Circle →ₜ* SU6) (z : Circle) : ℂ :=
  (((Y z : SU6) : Matrix (Fin 6) (Fin 6) ℂ) 0 0)

theorem scalarCoefficient_continuous (Y : Circle →ₜ* SU6) :
    Continuous (scalarCoefficient Y) := by
  exact (continuous_subtype_val.comp Y.continuous).matrix_elem 0 0

/-- Schur's lemma identifies the entire commuting matrix with the scalar read
from its `(0,0)` entry. -/
theorem commutingCircle_matrix_eq_smul_one
    (iota : ProductGroup →* SU6) (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    [Representation.IsIrreducible (definingRestriction iota)]
    (z : Circle) :
    (((Y z : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) =
      scalarCoefficient Y z • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  obtain ⟨c, hc⟩ := intertwiner_eq_smul_one_of_irreducible
    (definingRestriction iota)
    (commutingCircleIntertwiner iota Y hCommute z)
  have hLinear := congrArg Representation.IntertwiningMap.toLinearMap hc
  have hMatrix :
      (((Y z : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) =
        c • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
    apply Matrix.toLin'.injective
    rw [map_smul, Matrix.toLin'_one]
    change
      Matrix.toLin' (((Y z : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) =
        c • (LinearMap.id : RepSpace →ₗ[ℂ] RepSpace) at hLinear
    exact hLinear
  have hCoefficient : scalarCoefficient Y z = c := by
    have hEntry := congrArg
      (fun M : Matrix (Fin 6) (Fin 6) ℂ => M 0 0) hMatrix
    simpa [scalarCoefficient] using hEntry
  rw [hCoefficient]
  exact hMatrix

theorem scalarCoefficient_pow_six
    (iota : ProductGroup →* SU6) (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    [Representation.IsIrreducible (definingRestriction iota)]
    (z : Circle) :
    scalarCoefficient Y z ^ 6 = 1 :=
  scalar_coefficient_pow_six_of_mem_su6 (Y z) (scalarCoefficient Y z)
    (commutingCircle_matrix_eq_smul_one iota Y hCommute z)

/-- The finite target in which the scalar coefficient takes values. -/
abbrev SixthRoots := {c : ℂ // c ^ 6 = 1}

theorem sixthRoots_finite : Set.Finite {c : ℂ | c ^ 6 = 1} := by
  have hp : (X ^ 6 - 1 : ℂ[X]) ≠ 0 := by
    intro h
    have hEval := congrArg (fun p : ℂ[X] => p.eval 0) h
    norm_num at hEval
  apply (Polynomial.finite_setOfPred_isRoot hp).subset
  intro c hc
  change Polynomial.eval c (X ^ 6 - 1) = 0
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one]
  exact sub_eq_zero.mpr hc

noncomputable instance : Fintype SixthRoots :=
  Set.Finite.fintype sixthRoots_finite

noncomputable instance : DiscreteTopology SixthRoots :=
  isDiscrete_iff_discreteTopology.mp sixthRoots_finite.isDiscrete

/-- The scalar coefficient as a continuous map into the finite sixth-root
space. -/
def scalarRootMap
    (iota : ProductGroup →* SU6) (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    [Representation.IsIrreducible (definingRestriction iota)] :
    Circle → SixthRoots :=
  fun z => ⟨scalarCoefficient Y z,
    scalarCoefficient_pow_six iota Y hCommute z⟩

theorem scalarRootMap_continuous
    (iota : ProductGroup →* SU6) (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    [Representation.IsIrreducible (definingRestriction iota)] :
    Continuous (scalarRootMap iota Y hCommute) := by
  exact Continuous.subtype_mk (scalarCoefficient_continuous Y) _

@[simp]
theorem scalarCoefficient_one (Y : Circle →ₜ* SU6) :
    scalarCoefficient Y 1 = 1 := by
  simp [scalarCoefficient]

/-- Connectedness of the circle makes the scalar coefficient identically
one. -/
theorem scalarCoefficient_eq_one
    (iota : ProductGroup →* SU6) (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    [Representation.IsIrreducible (definingRestriction iota)]
    (z : Circle) : scalarCoefficient Y z = 1 := by
  have hConstant := TotallyDisconnectedSpace.eq_of_continuous
    (scalarRootMap iota Y hCommute)
    (scalarRootMap_continuous iota Y hCommute) z 1
  have hValue := congrArg Subtype.val hConstant
  change scalarCoefficient Y z = scalarCoefficient Y 1 at hValue
  rw [scalarCoefficient_one] at hValue
  exact hValue

/-- A continuous circle in the centralizer of an irreducible defining
restriction is the trivial homomorphism. -/
theorem commutingCircle_eq_one
    (iota : ProductGroup →* SU6) (Y : Circle →ₜ* SU6)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    [Representation.IsIrreducible (definingRestriction iota)] :
    Y = 1 := by
  apply ContinuousMonoidHom.ext
  intro z
  apply Subtype.ext
  have hMatrix := commutingCircle_matrix_eq_smul_one iota Y hCommute z
  rw [scalarCoefficient_eq_one iota Y hCommute z, one_smul] at hMatrix
  exact hMatrix

end

end ContinuousCentralizer
end GUT
