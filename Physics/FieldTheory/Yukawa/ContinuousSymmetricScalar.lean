import Physics.FieldTheory.Yukawa.SymmetricScalarYukawa
import Math.RepresentationTheory.Unitary.ContinuousConstructions
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear

open Math

/-!
# Physically admissible symmetric-form scalars

The algebraic symmetric-form representation has a jointly continuous finite
Hilbert model. For SU(6), Haar averaging then gives an actual continuous
unitary scalar representation, without an assumed scalar weight certificate.
-/

set_option autoImplicit false

namespace GUT.ContinuousSymmetricScalar

noncomputable section

open SymmetricScalarYukawa FiniteBasisHilbertization ContinuousUnitaryConstructions
open ContinuousRepresentationScope

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
variable (rho : Representation ℂ G V)

local instance scalarFree : Module.Free ℂ (Scalar rho) :=
  Module.Free.of_divisionRing ℂ (Scalar rho)

def scalarBasis := Module.finBasis ℂ (Scalar rho)

abbrev ScalarCopy := Copy (V := Scalar rho) (scalarBasis rho)

def seedRho : Representation ℂ G (ScalarCopy rho) :=
  basisCopyRepresentation (A := Scalar rho) (scalarBasis rho) (scalarRho rho)

def seedEquiv : Representation.Equiv (scalarRho rho) (seedRho rho) :=
  basisCopyRepresentationEquiv (A := Scalar rho) (scalarBasis rho) (scalarRho rho)

def matrixCoordinates : ScalarCopy rho →ₗ[ℂ]
    Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
  (LinearMap.BilinForm.toMatrix (Module.finBasis ℂ V)).toLinearMap.comp
    ((symmetricForms rho).toSubmodule.subtype.comp
      (Copy.valLinearEquiv (V := Scalar rho) (scalarBasis rho)).toLinearMap)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem matrixCoordinates_injective : Function.Injective (matrixCoordinates rho) := by
  intro x y h
  apply (Copy.valLinearEquiv (V := Scalar rho) (scalarBasis rho)).injective
  apply Subtype.ext
  exact (LinearMap.BilinForm.toMatrix (Module.finBasis ℂ V)).injective h

theorem seed_jointlyContinuous (h : IsJointlyContinuous rho) :
    IsJointlyContinuous (seedRho rho) := by
  apply jointlyContinuous_of_orbit
  intro s
  have he := (LinearMap.isClosedEmbedding_of_injective
    (LinearMap.ker_eq_bot.mpr (matrixCoordinates_injective rho))).isEmbedding
  apply he.continuous_iff.mpr
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  have hc (g : G) : matrixCoordinates rho (seedRho rho g s) i j =
      s.val.val (rho g⁻¹ (Module.finBasis ℂ V i)) (rho g⁻¹ (Module.finBasis ℂ V j)) := by
    change LinearMap.BilinForm.toMatrix (Module.finBasis ℂ V)
      (seedRho rho g s).val.val i j = _
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  simp_rw [Function.comp_apply, hc]
  exact (s.val.val.toContinuousBilinearMap.continuous.comp
    ((h.orbit (Module.finBasis ℂ V i)).comp continuous_inv)).clm_apply
      ((h.orbit (Module.finBasis ℂ V j)).comp continuous_inv)

end

end GUT.ContinuousSymmetricScalar
