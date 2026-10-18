import Math.LieGroups.E6.Minuscule.MatrixLieBasis
import Math.LieAlgebras.BasedLieComparison
import Math.LieAlgebras.PinnedGeckBasis
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Generator-preserving comparison with the pinned E6 and D5 Lie algebras

This constructs faithful 27-dimensional Lie algebra representations of the
actual scalar-extended Geck carriers. It does not integrate them to compact
groups or identify a global form.
-/

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

namespace Math.E6.Minuscule

open TauCeti.DynkinType TauCeti.E6Minuscule

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

theorem valid_D5 : (D 5).Valid := by decide

variable (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]

local instance : CharZero K := Algebra.charZero_of_charZero ℚ K

omit [IsAlgClosed K] in
private theorem generated_finrank :
    Module.finrank K (SerreMatrixBasis.generated K raisingMatrix loweringMatrix) = 78 := by
  rw [generated_eq_matrixLieAlgebra]
  exact matrixLieAlgebra_finrank K

omit [IsAlgClosed K] in
private theorem d5_generated_finrank :
    Module.finrank K (SerreMatrixBasis.generated K (raisingMatrix ∘ d5Node)
      (loweringMatrix ∘ d5Node)) = 45 := by
  rw [generated_eq_d5MatrixLieAlgebra]
  exact d5MatrixLieAlgebra_finrank K

def generatedGeckEquiv :
    SerreMatrixBasis.generated K raisingMatrix loweringMatrix ≃ₗ⁅K⁆
      E6.lieAlgebraBaseChange valid_E6 K :=
  BasedLieComparison.equiv (matrixCartanBasis K)
    (PinnedGeckBasis.numberedBasis E6 valid_E6 K) (by simp)
    (by rw [generated_finrank, PinnedGeckBasis.finrank_lieAlgebra]; rfl)

def d5GeneratedGeckEquiv :
    SerreMatrixBasis.generated K (raisingMatrix ∘ d5Node) (loweringMatrix ∘ d5Node) ≃ₗ⁅K⁆
      (D 5).lieAlgebraBaseChange valid_D5 K :=
  BasedLieComparison.equiv (d5MatrixCartanBasis K)
    (PinnedGeckBasis.numberedBasis (D 5) valid_D5 K) (by simp)
    (by rw [d5_generated_finrank, PinnedGeckBasis.finrank_lieAlgebra]; rfl)

def matrixGeckEquiv : matrixLieAlgebra K ≃ₗ⁅K⁆ E6.lieAlgebraBaseChange valid_E6 K :=
  (LieEquiv.ofEq _ _ (congrArg SetLike.coe (generated_eq_matrixLieAlgebra K).symm)).trans
    (generatedGeckEquiv K)

def d5MatrixGeckEquiv : d5MatrixLieAlgebra K ≃ₗ⁅K⁆ (D 5).lieAlgebraBaseChange valid_D5 K :=
  (LieEquiv.ofEq _ _ (congrArg SetLike.coe (generated_eq_d5MatrixLieAlgebra K).symm)).trans
    (d5GeneratedGeckEquiv K)

/-- The pinned E6 Lie algebra acts faithfully on the actual minuscule coordinates. -/
def geckRepresentation : E6.lieAlgebraBaseChange valid_E6 K →ₗ⁅K⁆ Matrix (Fin 27) (Fin 27) K :=
  (SerreMatrixBasis.generated K raisingMatrix loweringMatrix).incl.comp
    (generatedGeckEquiv K).symm.toLieHom

theorem geckRepresentation_injective : Function.Injective (geckRepresentation K) :=
  Subtype.val_injective.comp (generatedGeckEquiv K).symm.injective

@[simp] theorem geckRepresentation_h (i : Fin 6) :
    geckRepresentation K ((PinnedGeckBasis.numberedBasis E6 valid_E6 K).h i) =
      SerreMatrixBasis.castMatrix K (cartanGeneratorMatrix i) := by
  have he : generatedGeckEquiv K ((matrixCartanBasis K).h i) =
      (PinnedGeckBasis.numberedBasis E6 valid_E6 K).h i :=
    BasedLieComparison.equiv_h ..
  exact congrArg Subtype.val ((generatedGeckEquiv K).symm_apply_eq.mpr he.symm)

@[simp] theorem geckRepresentation_e (i : Fin 6) :
    geckRepresentation K ((PinnedGeckBasis.numberedBasis E6 valid_E6 K).e i) =
      SerreMatrixBasis.castMatrix K (raisingMatrix i) := by
  have he : generatedGeckEquiv K ((matrixCartanBasis K).e i) =
      (PinnedGeckBasis.numberedBasis E6 valid_E6 K).e i :=
    BasedLieComparison.equiv_e ..
  exact congrArg Subtype.val ((generatedGeckEquiv K).symm_apply_eq.mpr he.symm)

@[simp] theorem geckRepresentation_f (i : Fin 6) :
    geckRepresentation K ((PinnedGeckBasis.numberedBasis E6 valid_E6 K).f i) =
      SerreMatrixBasis.castMatrix K (loweringMatrix i) := by
  have he : generatedGeckEquiv K ((matrixCartanBasis K).f i) =
      (PinnedGeckBasis.numberedBasis E6 valid_E6 K).f i :=
    BasedLieComparison.equiv_f ..
  exact congrArg Subtype.val ((generatedGeckEquiv K).symm_apply_eq.mpr he.symm)

def d5GeckRepresentation : (D 5).lieAlgebraBaseChange valid_D5 K →ₗ⁅K⁆
    Matrix (Fin 27) (Fin 27) K :=
  (SerreMatrixBasis.generated K (raisingMatrix ∘ d5Node) (loweringMatrix ∘ d5Node)).incl.comp
    (d5GeneratedGeckEquiv K).symm.toLieHom

theorem d5GeckRepresentation_injective : Function.Injective (d5GeckRepresentation K) :=
  Subtype.val_injective.comp (d5GeneratedGeckEquiv K).symm.injective

@[simp] theorem d5GeckRepresentation_h (i : Fin 5) :
    d5GeckRepresentation K ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).h i) =
      SerreMatrixBasis.castMatrix K (cartanGeneratorMatrix (d5Node i)) := by
  have he : d5GeneratedGeckEquiv K ((d5MatrixCartanBasis K).h i) =
      (PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).h i :=
    BasedLieComparison.equiv_h ..
  exact congrArg Subtype.val ((d5GeneratedGeckEquiv K).symm_apply_eq.mpr he.symm)

@[simp] theorem d5GeckRepresentation_e (i : Fin 5) :
    d5GeckRepresentation K ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).e i) =
      SerreMatrixBasis.castMatrix K (raisingMatrix (d5Node i)) := by
  have he : d5GeneratedGeckEquiv K ((d5MatrixCartanBasis K).e i) =
      (PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).e i :=
    BasedLieComparison.equiv_e ..
  exact congrArg Subtype.val ((d5GeneratedGeckEquiv K).symm_apply_eq.mpr he.symm)

@[simp] theorem d5GeckRepresentation_f (i : Fin 5) :
    d5GeckRepresentation K ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).f i) =
      SerreMatrixBasis.castMatrix K (loweringMatrix (d5Node i)) := by
  have he : d5GeneratedGeckEquiv K ((d5MatrixCartanBasis K).f i) =
      (PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).f i :=
    BasedLieComparison.equiv_f ..
  exact congrArg Subtype.val ((d5GeneratedGeckEquiv K).symm_apply_eq.mpr he.symm)

/-- Transport of the verified D5 matrix inclusion between the actual Geck carriers. -/
def geckD5Inclusion : (D 5).lieAlgebraBaseChange valid_D5 K →ₗ⁅K⁆
    E6.lieAlgebraBaseChange valid_E6 K :=
  (matrixGeckEquiv K).toLieHom.comp
    ((d5MatrixInclusion K).comp (d5MatrixGeckEquiv K).symm.toLieHom)

theorem geckD5Inclusion_injective : Function.Injective (geckD5Inclusion K) :=
  (matrixGeckEquiv K).injective.comp
    ((d5MatrixInclusion_injective K).comp (d5MatrixGeckEquiv K).symm.injective)

@[simp] theorem geckRepresentation_inclusion (x : (D 5).lieAlgebraBaseChange valid_D5 K) :
    geckRepresentation K (geckD5Inclusion K x) = d5GeckRepresentation K x := by
  change ((generatedGeckEquiv K).symm ((generatedGeckEquiv K) _) :
    Matrix (Fin 27) (Fin 27) K) = _
  rw [LieEquiv.symm_apply_apply]
  rfl

@[simp] theorem geckD5Inclusion_h (i : Fin 5) :
    geckD5Inclusion K ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).h i) =
      (PinnedGeckBasis.numberedBasis E6 valid_E6 K).h (d5Node i) := by
  apply geckRepresentation_injective K
  exact (geckRepresentation_inclusion K _).trans
    ((d5GeckRepresentation_h K i).trans (geckRepresentation_h K (d5Node i)).symm)

@[simp] theorem geckD5Inclusion_e (i : Fin 5) :
    geckD5Inclusion K ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).e i) =
      (PinnedGeckBasis.numberedBasis E6 valid_E6 K).e (d5Node i) := by
  apply geckRepresentation_injective K
  exact (geckRepresentation_inclusion K _).trans
    ((d5GeckRepresentation_e K i).trans (geckRepresentation_e K (d5Node i)).symm)

@[simp] theorem geckD5Inclusion_f (i : Fin 5) :
    geckD5Inclusion K ((PinnedGeckBasis.numberedBasis (D 5) valid_D5 K).f i) =
      (PinnedGeckBasis.numberedBasis E6 valid_E6 K).f (d5Node i) := by
  apply geckRepresentation_injective K
  exact (geckRepresentation_inclusion K _).trans
    ((d5GeckRepresentation_f K i).trans (geckRepresentation_f K (d5Node i)).symm)

end

end Math.E6.Minuscule
