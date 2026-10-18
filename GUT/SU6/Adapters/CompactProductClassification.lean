import Math.RepresentationTheory.Decomposition.CompactProductFactorization
import GUT.SU6.Embeddings.ContinuousRepresentationScope

open Math

/-! # Compact product factors in the SU2/SU3 classification interface

This application section retains its existing declaration namespace.
-/

namespace GUT
namespace CompactProductFactorization
open Math.CompactProductFactorization
open CompactEmbeddingClassification ProductFactorization ExternalTensorProduct
open ContinuousRepresentationScope
open scoped MonoidAlgebra
noncomputable section

variable {G H E : Type*} [Group G] [Group H]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E]

section SU3SU2HighestWeightConsequences

universe u

variable {E₆ : Type u}
variable [NormedAddCommGroup E₆] [InnerProductSpace ℂ E₆]
variable [FiniteDimensional ℂ E₆]

open DifferentiatedRepresentationBridge

/-!
### Local differentiated factor witnesses

The semisimple embedding classification decomposition only invokes highest-weight theory on the two factor
representations extracted from an irreducible constituent of the restricted
six-dimensional defining representation.  The following certificate records
compact-real differentials for precisely those two factors.  It avoids the
stronger global assumption that every abstract continuous `SU(2)` and `SU(3)`
irrep has already been differentiated.
-/

/-- A continuous product-factor witness together with compact-real
differentials for its actual color and weak factors. -/
structure RealDifferentiableFactorWitness
    (tau : Representation ℂ ProductGroup E₆) where
  factor : ContinuousFactorWitness tau
  colorDifferential : SU3RealLieHomDerivativeAtIdentityAction
    (firstSubmoduleAsSubrepresentation tau factor.S).toRepresentation
  weakDifferential : SU2RealLieHomDerivativeAtIdentityAction
    (multiplicityRangeRepresentation tau
      (firstSubmoduleRepresentation tau factor.S) factor.u)

/-- Compact-real differentials on the two ambient factor restrictions of a
product representation.  Restriction to the concrete irreducible factors
selected by `ContinuousFactorWitness` is derived below. -/
structure RealDifferentiableProductAction
    (tau : Representation ℂ ProductGroup E₆) where
  colorDifferential : SU3RealLieHomDerivativeAtIdentityAction
    (firstRestriction tau)
  weakDifferential : SU2RealLieHomDerivativeAtIdentityAction
    (secondRestriction tau)

/-- Ambient real-linear identity differentials for the two factor
restrictions.  The Lie-homomorphism laws required downstream follow from the
one-parameter derivative identities. -/
structure RealLinearlyDifferentiableProductAction
    (tau : Representation ℂ ProductGroup E₆) where
  colorDifferential : SU3RealLinearDerivativeAtIdentityAction
    (firstRestriction tau)
  weakDifferential : SU2RealLinearDerivativeAtIdentityAction
    (secondRestriction tau)

namespace RealLinearlyDifferentiableProductAction

variable {tau : Representation ℂ ProductGroup E₆}

/-- Derive both compact-real Lie differentials by differentiating
conjugation, then reuse the existing product-factorization bridge. -/
def toRealDifferentiableProductAction
    (D : RealLinearlyDifferentiableProductAction tau) :
    RealDifferentiableProductAction tau where
  colorDifferential :=
    D.colorDifferential.toRealLieHomDerivativeAtIdentityAction
  weakDifferential :=
    D.weakDifferential.toRealLieHomDerivativeAtIdentityAction

end RealLinearlyDifferentiableProductAction

namespace RealDifferentiableProductAction

variable {tau : Representation ℂ ProductGroup E₆}

/-- A product-invariant subspace, regarded only as a subrepresentation of
the first-factor restriction. -/
def firstRestrictionSubrepresentation
    (S : Subrepresentation tau) : Subrepresentation (firstRestriction tau) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule := fun g _v hv =>
    S.apply_mem_toSubmodule (g, 1) hv

/-- A product-invariant subspace, regarded only as a subrepresentation of
the second-factor restriction. -/
def secondRestrictionSubrepresentation
    (S : Subrepresentation tau) : Subrepresentation (secondRestriction tau) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule := fun h _v hv =>
    S.apply_mem_toSubmodule (1, h) hv

omit [FiniteDimensional ℂ E₆] in
theorem firstRestrictionSubrepresentation_toRepresentation
    (S : Subrepresentation tau) :
    (firstRestrictionSubrepresentation S).toRepresentation =
      firstRestriction S.toRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  rfl

omit [FiniteDimensional ℂ E₆] in
theorem secondRestrictionSubrepresentation_toRepresentation
    (S : Subrepresentation tau) :
    (secondRestrictionSubrepresentation S).toRepresentation =
      secondRestriction S.toRepresentation := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro v
  rfl

/-- Ambient factor differentials descend to every invariant constituent of
the product representation. -/
def restrictToSubrepresentation
    (D : RealDifferentiableProductAction tau)
    (S : Subrepresentation tau) :
    RealDifferentiableProductAction S.toRepresentation where
  colorDifferential := by
    rw [← firstRestrictionSubrepresentation_toRepresentation S]
    exact D.colorDifferential.restrictToSubrepresentation
      (firstRestrictionSubrepresentation S)
  weakDifferential := by
    rw [← secondRestrictionSubrepresentation_toRepresentation S]
    exact D.weakDifferential.restrictToSubrepresentation
      (secondRestrictionSubrepresentation S)

/-- Ambient factor differentials restrict canonically to the actual color
subrepresentation and weak multiplicity range selected by a factor witness. -/
def toFactorWitness
    (D : RealDifferentiableProductAction tau)
    (F : ContinuousFactorWitness tau) :
    RealDifferentiableFactorWitness tau where
  factor := F
  colorDifferential :=
    D.colorDifferential.restrictToSubrepresentation
      (firstSubmoduleAsSubrepresentation tau F.S)
  weakDifferential :=
    D.weakDifferential.restrictToSubrepresentation
      (multiplicityRange tau
        (firstSubmoduleRepresentation tau F.S) F.u)

end RealDifferentiableProductAction

/-- An irreducible continuous unitary product representation with ambient
factor differentials has a locally differentiated factor witness. -/
theorem exists_realDifferentiableFactorWitness
    (tau : Representation ℂ ProductGroup E₆)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (D : RealDifferentiableProductAction tau) :
    Nonempty (RealDifferentiableFactorWitness tau) := by
  obtain ⟨F⟩ := exists_continuousFactorWitness tau hUnitary hContinuous
  exact ⟨D.toFactorWitness F⟩

namespace RealDifferentiableFactorWitness

variable {tau : Representation ℂ ProductGroup E₆}

/-- The local color differential gives the checked bounded `SU(3)` dimension
classification needed by semisimple embedding classification. -/
theorem color_dimension_mem_of_le_six
    (R : RealDifferentiableFactorWitness tau)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hDimension : Module.finrank ℂ E₆ ≤ 6) :
    Module.finrank ℂ
        (firstSubmoduleAsSubrepresentation tau R.factor.S).toSubmodule ∈
      ({1, 3, 6} : Finset ℕ) := by
  let colorRho :=
    (firstSubmoduleAsSubrepresentation tau R.factor.S).toRepresentation
  let : FiniteDimensional ℂ
      (firstSubmoduleAsSubrepresentation tau R.factor.S).toSubmodule :=
    R.factor.firstFactor.finiteDimensional
  let : Representation.IsIrreducible colorRho :=
    R.factor.firstFactor.irreducible
  let S := R.colorDifferential.toExponentialModelOfCompactGeneration
    |>.toIntegratedStandardLieModel.toStandardLieModel
  have hColorDimension :
      Module.finrank ℂ
          (firstSubmoduleAsSubrepresentation tau R.factor.S).toSubmodule ≤ 6 :=
    (Submodule.finrank_le
      (firstSubmoduleAsSubrepresentation tau R.factor.S).toSubmodule).trans
      hDimension
  rcases S.finrank_eq_one_or_three_or_six hColorDimension with h | h | h
  · simp [h]
  · simp [h]
  · simp [h]

omit [FiniteDimensional ℂ E₆] in
/-- The local weak differential determines the action of the nontrivial
`SU(2)` center from the weak-factor dimension. -/
theorem weak_center_action_eq_dimension_sign
    (R : RealDifferentiableFactorWitness tau)
    [Nontrivial E₆] [Representation.IsIrreducible tau] :
    multiplicityRangeRepresentation tau
        (firstSubmoduleRepresentation tau R.factor.S) R.factor.u
        su2CenterElement =
      ((-1 : ℂ) ^
          (Module.finrank ℂ
            (MultiplicityRangeSpace tau
              (firstSubmoduleRepresentation tau R.factor.S)
              R.factor.u) - 1)) •
        (LinearMap.id :
          MultiplicityRangeSpace tau
              (firstSubmoduleRepresentation tau R.factor.S) R.factor.u →ₗ[ℂ]
            MultiplicityRangeSpace tau
              (firstSubmoduleRepresentation tau R.factor.S) R.factor.u) := by
  let weakRho := multiplicityRangeRepresentation tau
    (firstSubmoduleRepresentation tau R.factor.S) R.factor.u
  let : FiniteDimensional ℂ
      (MultiplicityRangeSpace tau
        (firstSubmoduleRepresentation tau R.factor.S) R.factor.u) :=
    R.factor.secondFactor.finiteDimensional
  let : Representation.IsIrreducible weakRho :=
    R.factor.secondFactor.irreducible
  let S := R.weakDifferential.toGeneratedModelOfCompactGeneration
    |>.toIntegratedStandardLieModel.toStandardLieModel
  obtain ⟨C⟩ := S.toHighestWeightCertificate
  rw [C.center_action, C.center_exponent_eq_dimension_sub_one]

omit [FiniteDimensional ℂ E₆] in
/-- A one-dimensional extracted color factor is trivial, derived locally
from its compact-real differential. -/
theorem color_action_eq_id_of_finrank_eq_one
    (R : RealDifferentiableFactorWitness tau)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hDimension : Module.finrank ℂ
      (firstSubmoduleAsSubrepresentation tau R.factor.S).toSubmodule = 1) :
    ∀ g, (firstSubmoduleAsSubrepresentation tau R.factor.S).toRepresentation g =
      LinearMap.id := by
  let colorRho :=
    (firstSubmoduleAsSubrepresentation tau R.factor.S).toRepresentation
  let : FiniteDimensional ℂ
      (firstSubmoduleAsSubrepresentation tau R.factor.S).toSubmodule :=
    R.factor.firstFactor.finiteDimensional
  let : Representation.IsIrreducible colorRho :=
    R.factor.firstFactor.irreducible
  let S := R.colorDifferential.toExponentialModelOfCompactGeneration
    |>.toIntegratedStandardLieModel.toStandardLieModel
  exact S.action_eq_id_of_finrank_eq_one hDimension

omit [FiniteDimensional ℂ E₆] in
/-- A one-dimensional extracted weak factor is trivial, derived locally from
its compact-real differential. -/
theorem weak_action_eq_id_of_finrank_eq_one
    (R : RealDifferentiableFactorWitness tau)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hDimension : Module.finrank ℂ
      (MultiplicityRangeSpace tau
        (firstSubmoduleRepresentation tau R.factor.S) R.factor.u) = 1) :
    ∀ h, multiplicityRangeRepresentation tau
        (firstSubmoduleRepresentation tau R.factor.S) R.factor.u h =
      LinearMap.id := by
  let weakRho := multiplicityRangeRepresentation tau
    (firstSubmoduleRepresentation tau R.factor.S) R.factor.u
  let : FiniteDimensional ℂ
      (MultiplicityRangeSpace tau
        (firstSubmoduleRepresentation tau R.factor.S) R.factor.u) :=
    R.factor.secondFactor.finiteDimensional
  let : Representation.IsIrreducible weakRho :=
    R.factor.secondFactor.irreducible
  let S := R.weakDifferential.toGeneratedModelOfCompactGeneration
    |>.toIntegratedStandardLieModel.toStandardLieModel
  obtain ⟨C⟩ := S.toHighestWeightCertificate
  exact C.action_eq_id_of_finrank_eq_one hDimension

end RealDifferentiableFactorWitness

/-- Once the bounded irreducible-classification input is supplied, the
continuous factor witness immediately has the color dimension list and the
exact weak center sign required by semisimple embedding classification. -/
theorem exists_classified_continuousFactorWitness_of_lowDimensionalTheory
    (T : SU2SU3LowDimensionalTheory.{u})
    (tau : Representation ℂ ProductGroup E₆)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ E₆ = 6) :
    ∃ F : ContinuousFactorWitness tau,
      Module.finrank ℂ
          (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule ∈
            ({1, 3, 6} : Finset ℕ) ∧
        multiplicityRangeRepresentation tau
            (firstSubmoduleRepresentation tau F.S) F.u su2CenterElement =
          ((-1 : ℂ) ^
              (Module.finrank ℂ
                (MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) - 1)) •
            (LinearMap.id :
              MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u →ₗ[ℂ]
                MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) := by
  obtain ⟨F⟩ := exists_continuousFactorWitness tau hUnitary hContinuous
  refine ⟨F, ?_, ?_⟩
  · apply T.su3_dimension_mem_of_le_six
      (firstSubmoduleAsSubrepresentation tau F.S).toRepresentation
      F.firstFactor
    exact (Submodule.finrank_le
      (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule).trans_eq
      hDimension
  · exact T.su2_center_action_eq_dimension_sign
      (multiplicityRangeRepresentation tau
        (firstSubmoduleRepresentation tau F.S) F.u)
      F.secondFactor

/-- Compatibility wrapper for the original full highest-weight interface. -/
theorem exists_classified_continuousFactorWitness
    (T : SU2SU3HighestWeightTheory.{u})
    (tau : Representation ℂ ProductGroup E₆)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ E₆ = 6) :
    ∃ F : ContinuousFactorWitness tau,
      Module.finrank ℂ
          (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule ∈
            ({1, 3, 6} : Finset ℕ) ∧
        multiplicityRangeRepresentation tau
            (firstSubmoduleRepresentation tau F.S) F.u su2CenterElement =
          ((-1 : ℂ) ^
              (Module.finrank ℂ
                (MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) - 1)) •
            (LinearMap.id :
              MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u →ₗ[ℂ]
                MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) :=
  exists_classified_continuousFactorWitness_of_lowDimensionalTheory
    T.toLowDimensionalTheory tau hUnitary hContinuous hDimension

/-- The constituent-level form used after decomposing a six-dimensional
semisimple representation. -/
theorem exists_classified_continuousFactorWitness_of_dimension_le_six_of_lowDimensionalTheory
    (T : SU2SU3LowDimensionalTheory.{u})
    (tau : Representation ℂ ProductGroup E₆)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ E₆ ≤ 6) :
    ∃ F : ContinuousFactorWitness tau,
      Module.finrank ℂ
          (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule ∈
            ({1, 3, 6} : Finset ℕ) ∧
        multiplicityRangeRepresentation tau
            (firstSubmoduleRepresentation tau F.S) F.u su2CenterElement =
          ((-1 : ℂ) ^
              (Module.finrank ℂ
                (MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) - 1)) •
            (LinearMap.id :
              MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u →ₗ[ℂ]
                MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) := by
  obtain ⟨F⟩ := exists_continuousFactorWitness tau hUnitary hContinuous
  refine ⟨F, ?_, ?_⟩
  · apply T.su3_dimension_mem_of_le_six
      (firstSubmoduleAsSubrepresentation tau F.S).toRepresentation
      F.firstFactor
    exact (Submodule.finrank_le
      (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule).trans hDimension
  · exact T.su2_center_action_eq_dimension_sign
      (multiplicityRangeRepresentation tau
        (firstSubmoduleRepresentation tau F.S) F.u)
      F.secondFactor

/-- Compatibility wrapper for the original full highest-weight interface. -/
theorem exists_classified_continuousFactorWitness_of_dimension_le_six
    (T : SU2SU3HighestWeightTheory.{u})
    (tau : Representation ℂ ProductGroup E₆)
    [Nontrivial E₆] [Representation.IsIrreducible tau]
    (hUnitary : IsUnitaryRepresentation tau)
    (hContinuous : IsJointlyContinuous tau)
    (hDimension : Module.finrank ℂ E₆ ≤ 6) :
    ∃ F : ContinuousFactorWitness tau,
      Module.finrank ℂ
          (firstSubmoduleAsSubrepresentation tau F.S).toSubmodule ∈
            ({1, 3, 6} : Finset ℕ) ∧
        multiplicityRangeRepresentation tau
            (firstSubmoduleRepresentation tau F.S) F.u su2CenterElement =
          ((-1 : ℂ) ^
              (Module.finrank ℂ
                (MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) - 1)) •
            (LinearMap.id :
              MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u →ₗ[ℂ]
                MultiplicityRangeSpace tau
                  (firstSubmoduleRepresentation tau F.S) F.u) :=
  exists_classified_continuousFactorWitness_of_dimension_le_six_of_lowDimensionalTheory
    T.toLowDimensionalTheory tau hUnitary hContinuous hDimension

end SU3SU2HighestWeightConsequences

end
end CompactProductFactorization
end GUT
