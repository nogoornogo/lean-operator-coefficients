import Math.RepresentationTheory.Unitary.ContinuousConstructions
import GUT.SU6.Representations.ContinuousSU6Unitarization
import Math.LinearAlgebra.FiniteBasisHilbertization
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.Dual.Basis

open Math

/-!
# Constructions on continuous unitary SU(6) representations

This file supplies analytic closure constructions needed for concrete matter
benchmarks.  In particular, tensor products preserve joint continuity and
unitarity.  The continuity proof expands an arbitrary tensor in a finite
tensor-product basis, reducing the action to a finite sum of continuous
orbits.
-/

namespace GUT
namespace ContinuousUnitaryConstructions
open Math.ContinuousUnitaryConstructions

open CompactEmbeddingClassification
open ContinuousRepresentationScope
open ContinuousUnitaryWeightDecomposition
open FiniteBasisHilbertization
open scoped TensorProduct BigOperators

noncomputable section

universe u v w

namespace ContinuousUnitarySU6Representation

/-- A finite-basis Hilbert copy of the algebraic dual action. -/
def dualSeedRho (R : ContinuousUnitarySU6Representation) :
    Representation ℂ ActualRestriction.SU6
      (Copy (Module.finBasis ℂ R.V).dualBasis) :=
  basisCopyRepresentation (Module.finBasis ℂ R.V).dualBasis R.rho.dual

/-- Dual-basis orbit coordinates are matrix coefficients at the inverse
group element, hence continuous. -/
theorem dualSeedRho_jointlyContinuous
    (R : ContinuousUnitarySU6Representation) :
    IsJointlyContinuous (dualSeedRho R) := by
  apply basisCopyRepresentation_jointlyContinuous
  intro i
  rw [Copy.continuous_iff_coords]
  intro j
  simp only [Module.Basis.coord_apply, Module.Basis.dualBasis_repr]
  exact ((Module.finBasis ℂ R.V).dualBasis i).continuous_of_finiteDimensional.comp
    ((R.continuous_action.orbit (Module.finBasis ℂ R.V j)).comp continuous_inv)

/-- The contragredient action, with its inner product obtained by Haar
averaging. -/
def dual (R : ContinuousUnitarySU6Representation) :
    ContinuousUnitarySU6Representation :=
  ContinuousSU6Unitarization.model (dualSeedRho R)
    (dualSeedRho_jointlyContinuous R)

/-- Forgetting the Hilbert model recovers the usual algebraic dual. -/
def dualEquiv (R : ContinuousUnitarySU6Representation) :
    Representation.Equiv R.rho.dual (dual R).rho :=
  (basisCopyRepresentationEquiv (Module.finBasis ℂ R.V).dualBasis R.rho.dual).trans
    (ContinuousSU6Unitarization.modelEquiv (dualSeedRho R)
      (dualSeedRho_jointlyContinuous R))

/-- Tensor product in the bundled continuous-unitary `SU(6)` category. -/
def tensor
    (R S : ContinuousUnitarySU6Representation) :
    ContinuousUnitarySU6Representation where
  V := R.V ⊗[ℂ] S.V
  rho := R.rho.tprod S.rho
  unitary := unitary_tprod R.rho S.rho R.unitary S.unitary
  continuous_action := jointlyContinuous_tprod R.rho S.rho
    R.continuous_action S.continuous_action

end ContinuousUnitarySU6Representation

end
end ContinuousUnitaryConstructions
end GUT
