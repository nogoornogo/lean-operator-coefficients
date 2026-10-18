import Math.RepresentationTheory.Unitary.ContinuousAction
import GUT.SU6.Embeddings.HighestWeightBridge
import GUT.SU6.Embeddings.LowDimensionalCenterActions
import GUT.SU6.Embeddings.LowDimensionalConcreteIrreps
import GUT.SU6.Embeddings.DifferentiatedRepresentationBridge
import Mathlib.RepresentationTheory.Continuous.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

open Math

/-!
# Continuous finite-dimensional representation scope

`ContRepresentation` in mathlib only says that each group element acts by a
continuous linear map; it deliberately does not require continuity in the
group variable.  For compact Lie-group representation theory we therefore
record joint continuity of the action explicitly.
-/

namespace GUT
namespace ContinuousRepresentationScope

open Math.ContinuousRepresentationScope

open CompactEmbeddingClassification

noncomputable section

/-!
## Exact highest-weight classification interface

The construction of this object for all continuous irreducibles is the
remaining Lie-theoretic input.  Its consequences needed by semisimple embedding classification are proved
below, so no downstream theorem needs to assume dimension lists or center
signs separately.
-/

universe u

/-- The precise output of the `SU(2)` and `SU(3)` highest-weight
classification required by semisimple embedding classification. -/
structure SU2SU3HighestWeightTheory : Prop where
  su2_certificate :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty (HighestWeightBridge.SU2HighestWeightCertificate rho)
  su3_certificate :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty (HighestWeightBridge.SU3HighestWeightCertificate rho)

/-- A sharper construction interface in which the `SU(2)` dimension formula
is derived from an irreducible action of the concrete standard `sl₂(ℂ)`
matrix algebra.  The standard triple and its spanning theorem are checked;
only the group-to-Lie bridge, the weak-center exponential, triviality of
one-dimensional characters, and the independent `SU(3)` highest-weight
theorem remain as inputs. -/
structure SU2LieSU3HighestWeightTheory : Prop where
  su2_lieModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty (HighestWeightBridge.SU2StandardLieModel rho)
  su3_certificate :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty (HighestWeightBridge.SU3HighestWeightCertificate rho)

/-- The exact low-dimensional representation-theoretic output consumed by
semisimple embedding classification.  This interface deliberately does not require a full Weyl dimension
formula in dimensions which cannot occur in the six-dimensional defining
restriction. -/
structure SU2SU3LowDimensionalTheory : Prop where
  su3_dimension_mem_of_le_six :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Module.finrank ℂ W ≤ 6 →
          Module.finrank ℂ W ∈ ({1, 3, 6} : Finset ℕ)
  su2_center_action_eq_dimension_sign :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        rho su2CenterElement =
          ((-1 : ℂ) ^ (Module.finrank ℂ W - 1)) •
            (LinearMap.id : W →ₗ[ℂ] W)
  su2_action_eq_id_of_finrank_eq_one :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Module.finrank ℂ W = 1 → ∀ g, rho g = LinearMap.id
  su3_action_eq_id_of_finrank_eq_one :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Module.finrank ℂ W = 1 → ∀ g, rho g = LinearMap.id

/-- A construction interface based entirely on the two fixed standard matrix
Lie algebras.  Its construction from jointly continuous group actions is the
remaining analytic differentiation/integration bridge; all ensuing
low-dimensional Lie-algebra classification is checked in Lean. -/
structure SU2SU3StandardLieTheory : Prop where
  su2_lieModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty (HighestWeightBridge.SU2StandardLieModel rho)
  su3_lieModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty (HighestWeightBridge.SU3StandardLieModel rho)

/-- A narrower analytic interface.  It asks for differentiated standard Lie
actions, stability of Lie submodules under the original group action, the
`SU(2)` center exponential formula, and zero-differential integration.  Group
irreducibility is already part of `IsContinuousFiniteDimensionalIrrep` and is
converted to Lie irreducibility by a checked theorem. -/
structure SU2SU3IntegratedLieTheory : Prop where
  su2_integratedModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (HighestWeightBridge.SU2IntegratedStandardLieModel rho)
  su3_integratedModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (HighestWeightBridge.SU3IntegratedStandardLieModel rho)

/-- The analytic interface after the general operator-exponential argument has
been discharged.  It asks only for differentiated standard Lie actions, a
finite-product exponential generating family with action compatibility, and
the `SU(2)` center formula. -/
structure SU2SU3ExponentialLieTheory : Prop where
  su2_exponentialModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (HighestWeightBridge.SU2ExponentiallyIntegratedStandardLieModel rho)
  su3_exponentialModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (HighestWeightBridge.SU3ExponentiallyIntegratedStandardLieModel rho)

/-- The sharper exponential interface in which the `SU(2)` center sign is
derived from a distinguished `pi * I * H` generator rather than supplied as
an independent certificate. -/
structure SU2SU3GeneratedExponentialLieTheory : Prop where
  su2_generatedExponentialModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (HighestWeightBridge.SU2GeneratedExponentialStandardLieModel rho)
  su3_exponentialModel :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (HighestWeightBridge.SU3ExponentiallyIntegratedStandardLieModel rho)

/-- The concrete compact-exponential source interface.  Its two global fields
ask whether the standard matrix exponential is onto `SU(2)` and `SU(3)`; its
representation fields ask for the differentiated action and the standard
identity `rho(exp X) = exp(d rho X)`.  Everything after these facts is proved
by the checked semisimple embedding classification integration and low-dimensional classification chain. -/
structure SU2SU3CompactExponentialLieTheory : Prop where
  su2_exp_surjective : Function.Surjective
    (SpecialUnitaryLieAlgebra.CompactRealForm.expSpecialUnitary
      (n := Fin 2))
  su3_exp_surjective : Function.Surjective
    (SpecialUnitaryLieAlgebra.CompactRealForm.expSpecialUnitary
      (n := Fin 3))
  su2_differentiatedAction :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (SpecialUnitaryLieAlgebra.SU2DifferentiatedExponentialAction rho)
  su3_differentiatedAction :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (SpecialUnitaryLieAlgebra.SU3DifferentiatedExponentialAction rho)

/-- The compact-generation interface after the group-dependent matrix theorem
has been discharged.  Its only fields are representation-dependent:
differentiate each intended jointly continuous irreducible action and prove
`rho(exp X) = exp(d rho X)` on the concrete compact real form. -/
structure SU2SU3DifferentiatedExponentialLieTheory : Prop where
  su2_differentiatedAction :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (SpecialUnitaryLieAlgebra.SU2DifferentiatedExponentialAction rho)
  su3_differentiatedAction :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (SpecialUnitaryLieAlgebra.SU3DifferentiatedExponentialAction rho)

/-- The representation-dependent semisimple embedding classification interface after exponential
compatibility has been proved from the one-parameter subgroup theorem.  It
asks for a standard Lie action and identifies that action only with the
derivative at zero of each compact one-parameter subgroup. -/
structure SU2SU3DerivativeAtIdentityLieTheory : Prop where
  su2_derivativeAction :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (DifferentiatedRepresentationBridge.SU2DerivativeAtIdentityAction rho)
  su3_derivativeAction :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (DifferentiatedRepresentationBridge.SU3DerivativeAtIdentityAction rho)

/-- The same source interface in its intrinsic smooth-representation form:
the differential is supplied as a complex Lie algebra homomorphism into
`End(W)`, and the derivative identity is checked only on the compact real
form.  The induced `LieModule` instances are constructed internally. -/
structure SU2SU3LieHomDerivativeTheory : Prop where
  su2_lieHomDerivative :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (DifferentiatedRepresentationBridge.SU2LieHomDerivativeAtIdentityAction rho)
  su3_lieHomDerivative :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (DifferentiatedRepresentationBridge.SU3LieHomDerivativeAtIdentityAction rho)

/-- The source interface closest to ordinary Lie-group differentiation.  It
asks only for real Lie-hom differentials on the compact Lie algebras
`su(2)` and `su(3)` and their defining derivative identities.  Their complex
extensions to `sl(2,C)` and `sl(3,C)` are constructed internally. -/
structure SU2SU3RealLieHomDerivativeTheory : Prop where
  su2_realLieHomDerivative :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU2 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (DifferentiatedRepresentationBridge.SU2RealLieHomDerivativeAtIdentityAction rho)
  su3_realLieHomDerivative :
    ∀ {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
      (rho : Representation ℂ SU3 W),
      IsContinuousFiniteDimensionalIrrep rho →
        Nonempty
          (DifferentiatedRepresentationBridge.SU3RealLieHomDerivativeAtIdentityAction rho)

namespace SU2LieSU3HighestWeightTheory

/-- The checked `sl₂` lowering-string theorem upgrades the sharper Lie
interface to the downstream highest-weight interface used by semisimple embedding classification. -/
theorem toSU2SU3HighestWeightTheory
    (T : SU2LieSU3HighestWeightTheory.{u}) :
    SU2SU3HighestWeightTheory.{u} where
  su2_certificate := by
    intro W _ _ _ rho hRho
    let : FiniteDimensional ℂ W := hRho.finiteDimensional
    obtain ⟨S⟩ := T.su2_lieModel rho hRho
    exact S.toHighestWeightCertificate
  su3_certificate := T.su3_certificate

end SU2LieSU3HighestWeightTheory

namespace SU2SU3HighestWeightTheory

/-- The highest-weight theorem reduces every continuous `SU(3)` irrep of
dimension at most six to dimensions `1`, `3`, or `6`. -/
theorem su3_dimension_mem_of_le_six
    (T : SU2SU3HighestWeightTheory.{u})
    {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (rho : Representation ℂ SU3 W)
    (hRho : IsContinuousFiniteDimensionalIrrep rho)
    (hDim : Module.finrank ℂ W ≤ 6) :
    Module.finrank ℂ W ∈ ({1, 3, 6} : Finset ℕ) := by
  let : FiniteDimensional ℂ W := hRho.finiteDimensional
  obtain ⟨C⟩ := T.su3_certificate rho hRho
  exact LowDimensionalIrreps.su3_dimension_mem_of_dimension_le_six
    C.firstWeight C.secondWeight (Module.finrank ℂ W)
    C.dimension_formula hDim

/-- The weak center sign of every continuous `SU(2)` irrep is determined by
its dimension. -/
theorem su2_center_action_eq_dimension_sign
    (T : SU2SU3HighestWeightTheory.{u})
    {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (rho : Representation ℂ SU2 W)
    (hRho : IsContinuousFiniteDimensionalIrrep rho) :
    rho su2CenterElement =
      ((-1 : ℂ) ^ (Module.finrank ℂ W - 1)) •
        (LinearMap.id : W →ₗ[ℂ] W) := by
  let : FiniteDimensional ℂ W := hRho.finiteDimensional
  let : Representation.IsIrreducible rho := hRho.irreducible
  obtain ⟨C⟩ := T.su2_certificate rho hRho
  rw [C.center_action, C.center_exponent_eq_dimension_sub_one]

theorem su2_action_eq_id_of_finrank_eq_one
    (T : SU2SU3HighestWeightTheory.{u})
    {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (rho : Representation ℂ SU2 W)
    (hRho : IsContinuousFiniteDimensionalIrrep rho)
    (hDimension : Module.finrank ℂ W = 1) :
    ∀ g, rho g = LinearMap.id := by
  let : FiniteDimensional ℂ W := hRho.finiteDimensional
  obtain ⟨C⟩ := T.su2_certificate rho hRho
  exact C.action_eq_id_of_finrank_eq_one hDimension

theorem su3_action_eq_id_of_finrank_eq_one
    (T : SU2SU3HighestWeightTheory.{u})
    {W : Type u} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (rho : Representation ℂ SU3 W)
    (hRho : IsContinuousFiniteDimensionalIrrep rho)
    (hDimension : Module.finrank ℂ W = 1) :
    ∀ g, rho g = LinearMap.id := by
  let : FiniteDimensional ℂ W := hRho.finiteDimensional
  obtain ⟨C⟩ := T.su3_certificate rho hRho
  exact C.action_eq_id_of_finrank_eq_one hDimension

/-- A full highest-weight theory supplies, in particular, the bounded output
actually used by semisimple embedding classification. -/
theorem toLowDimensionalTheory
    (T : SU2SU3HighestWeightTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} where
  su3_dimension_mem_of_le_six := T.su3_dimension_mem_of_le_six
  su2_center_action_eq_dimension_sign :=
    T.su2_center_action_eq_dimension_sign
  su2_action_eq_id_of_finrank_eq_one :=
    T.su2_action_eq_id_of_finrank_eq_one
  su3_action_eq_id_of_finrank_eq_one :=
    T.su3_action_eq_id_of_finrank_eq_one

end SU2SU3HighestWeightTheory

namespace SU2SU3IntegratedLieTheory

/-- Integration-stability and group irreducibility construct the standard
Lie-model package consumed by the checked low-dimensional classification. -/
theorem toStandardLieTheory
    (T : SU2SU3IntegratedLieTheory.{u}) :
    SU2SU3StandardLieTheory.{u} where
  su2_lieModel := by
    intro W _ _ _ rho hRho
    let : Representation.IsIrreducible rho := hRho.irreducible
    obtain ⟨S⟩ := T.su2_integratedModel rho hRho
    exact ⟨S.toStandardLieModel⟩
  su3_lieModel := by
    intro W _ _ _ rho hRho
    let : Representation.IsIrreducible rho := hRho.irreducible
    obtain ⟨S⟩ := T.su3_integratedModel rho hRho
    exact ⟨S.toStandardLieModel⟩

end SU2SU3IntegratedLieTheory

namespace SU2SU3ExponentialLieTheory

/-- Finite-dimensional operator exponentials turn the local exponential data
into the global integration-stability package. -/
theorem toIntegratedLieTheory
    (T : SU2SU3ExponentialLieTheory.{u}) :
    SU2SU3IntegratedLieTheory.{u} where
  su2_integratedModel := by
    intro W _ _ _ rho hRho
    obtain ⟨S⟩ := T.su2_exponentialModel rho hRho
    exact ⟨S.toIntegratedStandardLieModel⟩
  su3_integratedModel := by
    intro W _ _ _ rho hRho
    obtain ⟨S⟩ := T.su3_exponentialModel rho hRho
    exact ⟨S.toIntegratedStandardLieModel⟩

theorem toStandardLieTheory
    (T : SU2SU3ExponentialLieTheory.{u}) :
    SU2SU3StandardLieTheory.{u} :=
  T.toIntegratedLieTheory.toStandardLieTheory

end SU2SU3ExponentialLieTheory

namespace SU2SU3GeneratedExponentialLieTheory

/-- The distinguished center generator supplies the only field present in
`SU2SU3ExponentialLieTheory` that is not ordinary exponential-generation
data. -/
theorem toExponentialLieTheory
    (T : SU2SU3GeneratedExponentialLieTheory.{u}) :
    SU2SU3ExponentialLieTheory.{u} where
  su2_exponentialModel := by
    intro W _ _ _ rho hRho
    obtain ⟨S⟩ := T.su2_generatedExponentialModel rho hRho
    exact ⟨S.toExponentiallyIntegratedStandardLieModel⟩
  su3_exponentialModel := T.su3_exponentialModel

theorem toIntegratedLieTheory
    (T : SU2SU3GeneratedExponentialLieTheory.{u}) :
    SU2SU3IntegratedLieTheory.{u} :=
  T.toExponentialLieTheory.toIntegratedLieTheory

theorem toStandardLieTheory
    (T : SU2SU3GeneratedExponentialLieTheory.{u}) :
    SU2SU3StandardLieTheory.{u} :=
  T.toExponentialLieTheory.toStandardLieTheory

end SU2SU3GeneratedExponentialLieTheory

namespace SU2SU3CompactExponentialLieTheory

/-- The concrete compact-exponential hypotheses construct the sharper
generated-exponential theory without any additional representation-theoretic
certificate. -/
theorem toGeneratedExponentialLieTheory
    (T : SU2SU3CompactExponentialLieTheory.{u}) :
    SU2SU3GeneratedExponentialLieTheory.{u} where
  su2_generatedExponentialModel := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su2_differentiatedAction rho hRho
    exact ⟨D.toGeneratedModel T.su2_exp_surjective⟩
  su3_exponentialModel := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su3_differentiatedAction rho hRho
    exact ⟨D.toExponentialModel T.su3_exp_surjective⟩

end SU2SU3CompactExponentialLieTheory

namespace SU2SU3DifferentiatedExponentialLieTheory

/-- The checked finite-matrix generation theorem upgrades differentiated
actions directly to the generated-exponential theory used downstream. -/
theorem toGeneratedExponentialLieTheory
    (T : SU2SU3DifferentiatedExponentialLieTheory.{u}) :
    SU2SU3GeneratedExponentialLieTheory.{u} where
  su2_generatedExponentialModel := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su2_differentiatedAction rho hRho
    exact ⟨D.toGeneratedModelOfCompactGeneration⟩
  su3_exponentialModel := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su3_differentiatedAction rho hRho
    exact ⟨D.toExponentialModelOfCompactGeneration⟩

end SU2SU3DifferentiatedExponentialLieTheory

namespace SU2SU3DerivativeAtIdentityLieTheory

/-- The derivative-at-identity certificates imply the full exponential
compatibility certificates by uniqueness of differentiable one-parameter
subgroups. -/
theorem toDifferentiatedExponentialLieTheory
    (T : SU2SU3DerivativeAtIdentityLieTheory.{u}) :
    SU2SU3DifferentiatedExponentialLieTheory.{u} where
  su2_differentiatedAction := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su2_derivativeAction rho hRho
    exact ⟨D.toDifferentiatedExponentialAction⟩
  su3_differentiatedAction := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su3_derivativeAction rho hRho
    exact ⟨D.toDifferentiatedExponentialAction⟩

/-- Hence derivative-at-identity data reaches the generated-exponential
models consumed by the checked highest-weight classification chain. -/
theorem toGeneratedExponentialLieTheory
    (T : SU2SU3DerivativeAtIdentityLieTheory.{u}) :
    SU2SU3GeneratedExponentialLieTheory.{u} :=
  T.toDifferentiatedExponentialLieTheory.toGeneratedExponentialLieTheory

end SU2SU3DerivativeAtIdentityLieTheory

namespace SU2SU3LieHomDerivativeTheory

/-- Pulling the tautological endomorphism action back along each differential
constructs the derivative-at-identity theory used by the checked integration
chain. -/
theorem toDerivativeAtIdentityLieTheory
    (T : SU2SU3LieHomDerivativeTheory.{u}) :
    SU2SU3DerivativeAtIdentityLieTheory.{u} where
  su2_derivativeAction := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su2_lieHomDerivative rho hRho
    exact ⟨D.toDerivativeAtIdentityAction⟩
  su3_derivativeAction := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su3_lieHomDerivative rho hRho
    exact ⟨D.toDerivativeAtIdentityAction⟩

/-- Hence intrinsic Lie-hom differentials reach the generated exponential
models without an independently assumed exponential-compatibility axiom. -/
theorem toGeneratedExponentialLieTheory
    (T : SU2SU3LieHomDerivativeTheory.{u}) :
    SU2SU3GeneratedExponentialLieTheory.{u} :=
  T.toDerivativeAtIdentityLieTheory.toGeneratedExponentialLieTheory

end SU2SU3LieHomDerivativeTheory

namespace SU2SU3RealLieHomDerivativeTheory

/-- Explicit complexification of each compact-real differential supplies the
complex Lie-hom source interface. -/
theorem toLieHomDerivativeTheory
    (T : SU2SU3RealLieHomDerivativeTheory.{u}) :
    SU2SU3LieHomDerivativeTheory.{u} where
  su2_lieHomDerivative := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su2_realLieHomDerivative rho hRho
    exact ⟨D.toLieHomDerivativeAtIdentityAction⟩
  su3_lieHomDerivative := by
    intro W _ _ _ rho hRho
    obtain ⟨D⟩ := T.su3_realLieHomDerivative rho hRho
    exact ⟨D.toLieHomDerivativeAtIdentityAction⟩

/-- Thus compact-real differentials reach the generated exponential models
used by the checked highest-weight chain. -/
theorem toGeneratedExponentialLieTheory
    (T : SU2SU3RealLieHomDerivativeTheory.{u}) :
    SU2SU3GeneratedExponentialLieTheory.{u} :=
  T.toLieHomDerivativeTheory.toGeneratedExponentialLieTheory

end SU2SU3RealLieHomDerivativeTheory

namespace SU2SU3StandardLieTheory

/-- The checked `sl₂` lowering string and concrete `sl₃` highest-weight
classification turn standard differentiated models into the exact bounded
classification package used by semisimple embedding classification. -/
theorem toLowDimensionalTheory
    (T : SU2SU3StandardLieTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} where
  su3_dimension_mem_of_le_six := by
    intro W _ _ _ rho hRho hDimension
    let : FiniteDimensional ℂ W := hRho.finiteDimensional
    obtain ⟨S⟩ := T.su3_lieModel rho hRho
    rcases S.finrank_eq_one_or_three_or_six hDimension with h | h | h
    · simp [h]
    · simp [h]
    · simp [h]
  su2_center_action_eq_dimension_sign := by
    intro W _ _ _ rho hRho
    let : FiniteDimensional ℂ W := hRho.finiteDimensional
    let : Representation.IsIrreducible rho := hRho.irreducible
    obtain ⟨S⟩ := T.su2_lieModel rho hRho
    obtain ⟨C⟩ := S.toHighestWeightCertificate
    rw [C.center_action, C.center_exponent_eq_dimension_sub_one]
  su2_action_eq_id_of_finrank_eq_one := by
    intro W _ _ _ rho hRho hDimension
    let : FiniteDimensional ℂ W := hRho.finiteDimensional
    obtain ⟨S⟩ := T.su2_lieModel rho hRho
    obtain ⟨C⟩ := S.toHighestWeightCertificate
    exact C.action_eq_id_of_finrank_eq_one hDimension
  su3_action_eq_id_of_finrank_eq_one := by
    intro W _ _ _ rho hRho hDimension
    let : FiniteDimensional ℂ W := hRho.finiteDimensional
    obtain ⟨S⟩ := T.su3_lieModel rho hRho
    exact S.action_eq_id_of_finrank_eq_one hDimension

end SU2SU3StandardLieTheory

namespace SU2SU3IntegratedLieTheory

theorem toLowDimensionalTheory
    (T : SU2SU3IntegratedLieTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toStandardLieTheory.toLowDimensionalTheory

end SU2SU3IntegratedLieTheory

namespace SU2SU3ExponentialLieTheory

theorem toLowDimensionalTheory
    (T : SU2SU3ExponentialLieTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toIntegratedLieTheory.toLowDimensionalTheory

end SU2SU3ExponentialLieTheory

namespace SU2SU3GeneratedExponentialLieTheory

theorem toLowDimensionalTheory
    (T : SU2SU3GeneratedExponentialLieTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toExponentialLieTheory.toLowDimensionalTheory

end SU2SU3GeneratedExponentialLieTheory

namespace SU2SU3CompactExponentialLieTheory

theorem toLowDimensionalTheory
    (T : SU2SU3CompactExponentialLieTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toGeneratedExponentialLieTheory.toLowDimensionalTheory

end SU2SU3CompactExponentialLieTheory

namespace SU2SU3DifferentiatedExponentialLieTheory

theorem toLowDimensionalTheory
    (T : SU2SU3DifferentiatedExponentialLieTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toGeneratedExponentialLieTheory.toLowDimensionalTheory

end SU2SU3DifferentiatedExponentialLieTheory

namespace SU2SU3DerivativeAtIdentityLieTheory

theorem toLowDimensionalTheory
    (T : SU2SU3DerivativeAtIdentityLieTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toGeneratedExponentialLieTheory.toLowDimensionalTheory

end SU2SU3DerivativeAtIdentityLieTheory

namespace SU2SU3LieHomDerivativeTheory

theorem toLowDimensionalTheory
    (T : SU2SU3LieHomDerivativeTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toGeneratedExponentialLieTheory.toLowDimensionalTheory

end SU2SU3LieHomDerivativeTheory

namespace SU2SU3RealLieHomDerivativeTheory

theorem toLowDimensionalTheory
    (T : SU2SU3RealLieHomDerivativeTheory.{u}) :
    SU2SU3LowDimensionalTheory.{u} :=
  T.toGeneratedExponentialLieTheory.toLowDimensionalTheory

end SU2SU3RealLieHomDerivativeTheory

/-!
## The defining `SU(6)` restriction
-/

/-- The defining matrix action of `SU(6)` on `C^6` is jointly continuous. -/
theorem fundamentalRepresentation_jointlyContinuous :
    IsJointlyContinuous FundamentalRepresentation.rho := by
  change Continuous fun p : SU6 × (Fin 6 → ℂ) =>
    Matrix.mulVec (((p.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ)) p.2
  exact
    (continuous_subtype_val.comp continuous_fst).matrix_mulVec continuous_snd

/-- Restriction of the defining action along a continuous proposed embedding
has the continuity required by compact representation theory. -/
theorem definingRestriction_jointlyContinuous
    (iota : ProductGroup →ₜ* SU6) :
    IsJointlyContinuous (definingRestriction (iota : ProductGroup →* SU6)) :=
  fundamentalRepresentation_jointlyContinuous.comp iota

/-- The same jointly continuous defining restriction on the Euclidean norm
model used by the unitary complete-reducibility proof. -/
theorem euclideanDefiningRestriction_jointlyContinuous
    (iota : ProductGroup →ₜ* SU6) :
    IsJointlyContinuous
      (euclideanDefiningRestriction (iota : ProductGroup →* SU6)) := by
  change Continuous fun p : ProductGroup × EuclideanRepSpace =>
    WithLp.toLp 2
      (Matrix.mulVec
        (((iota p.1 : SU6) : Matrix (Fin 6) (Fin 6) ℂ))
        (WithLp.ofLp p.2))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 6 => ℂ)).comp
  exact (continuous_subtype_val.comp (iota.continuous.comp continuous_fst)).matrix_mulVec
    ((PiLp.continuous_ofLp 2 (fun _ : Fin 6 => ℂ)).comp continuous_snd)

/-!
## The concrete weak doublet
-/

open LowDimensionalCenterActions

/-- The directly constructed defining representation of `SU(2)` has a
jointly continuous action. -/
theorem su2Defining_jointlyContinuous :
    IsJointlyContinuous su2Defining := by
  change Continuous fun p : SU2 × WeakStd =>
    Matrix.mulVec (((p.1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ)) p.2
  exact
    (continuous_subtype_val.comp continuous_fst).matrix_mulVec continuous_snd

/-- The weak doublet is an actual object in the continuous finite-dimensional
irreducible scope, not merely a dimension label. -/
theorem su2Defining_isContinuousFiniteDimensionalIrrep :
    IsContinuousFiniteDimensionalIrrep su2Defining where
  finiteDimensional := inferInstance
  irreducible := su2Defining_isIrreducible
  continuous_action := su2Defining_jointlyContinuous

/-!
## The concrete color triplet
-/

open LowDimensionalConcreteIrreps

theorem trivialLine_jointlyContinuous
    (K : Type*) [Group K] [TopologicalSpace K] :
    IsJointlyContinuous (trivialLine K) := by
  change Continuous fun p : K × ℂ => p.2
  exact continuous_snd

theorem su2Trivial_isContinuousFiniteDimensionalIrrep :
    IsContinuousFiniteDimensionalIrrep (trivialLine SU2) where
  finiteDimensional := inferInstance
  irreducible := trivialLine_isIrreducible SU2
  continuous_action := trivialLine_jointlyContinuous SU2

theorem su3Trivial_isContinuousFiniteDimensionalIrrep :
    IsContinuousFiniteDimensionalIrrep (trivialLine SU3) where
  finiteDimensional := inferInstance
  irreducible := trivialLine_isIrreducible SU3
  continuous_action := trivialLine_jointlyContinuous SU3

theorem su3Defining_jointlyContinuous :
    IsJointlyContinuous su3Defining := by
  change Continuous fun p : SU3 × ColorStd =>
    Matrix.mulVec (((p.1 : SU3) : Matrix (Fin 3) (Fin 3) ℂ)) p.2
  exact
    (continuous_subtype_val.comp continuous_fst).matrix_mulVec continuous_snd

theorem su3Defining_isContinuousFiniteDimensionalIrrep :
    IsContinuousFiniteDimensionalIrrep su3Defining where
  finiteDimensional := inferInstance
  irreducible := su3Defining_isIrreducible
  continuous_action := su3Defining_jointlyContinuous

end

end ContinuousRepresentationScope
end GUT
