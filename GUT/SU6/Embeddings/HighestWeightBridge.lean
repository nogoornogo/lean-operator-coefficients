import GUT.SU6.Embeddings.CompactEmbeddingClassification
import GUT.SU6.Embeddings.ExponentialRepresentationBridge
import GUT.SU6.Embeddings.LowDimensionalIrreps
import Math.Algebra.Lie.Sl2String
import Math.Algebra.Lie.Sl3HighestWeightExistence
import Math.Algebra.Lie.StandardSl2
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Tactic

open Math

/-!
# Highest-weight certificates needed by semisimple embedding classification

Mathlib currently has no classification theorem for continuous
finite-dimensional complex representations of `SU(2)` or `SU(3)`.  This file
isolates the exact output needed from that theory and proves the downstream
bridges which do not require rebuilding the classification itself.

In particular, a highest-weight vector determines the action of a central
element on the entire irreducible representation.  This follows from Schur's
lemma and is proved below rather than included as certificate data.
-/

namespace GUT
namespace HighestWeightBridge

open CompactEmbeddingClassification ExponentialRepresentationBridge
  LowDimensionalIrreps

noncomputable section

section CentralCharacter

variable {G V : Type*} [Group G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- On an irreducible complex representation, the eigenvalue of a central
element on one nonzero vector determines its action everywhere. -/
theorem central_action_eq_smul_id_of_eigenvector
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho]
    (z : G) (hz : z ∈ Submonoid.center G)
    (a : ℂ) (v : V) (hv : v ≠ 0) (heigen : rho z v = a • v) :
    rho z = a • (LinearMap.id : V →ₗ[ℂ] V) := by
  let f : Representation.IntertwiningMap rho rho :=
    Representation.IntertwiningMap.centralMul rho z hz
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := rho)).2 f
  have hop : rho z = c • (LinearMap.id : V →ₗ[ℂ] V) := by
    have hmap := congrArg Representation.IntertwiningMap.toLinearMap hc.symm
    apply LinearMap.ext
    intro w
    have hmapw := LinearMap.congr_fun hmap w
    change rho z w = c • w at hmapw
    exact hmapw
  have hca : c = a := by
    apply smul_left_injective ℂ hv
    calc
      c • v = rho z v := by rw [hop]; rfl
      _ = a • v := heigen
  simpa [hca] using hop

end CentralCharacter

/-!
## Irreducibility across differentiation
-/

open scoped MonoidAlgebra

/-- If every subspace invariant under a supplied Lie action is also invariant
under the group representation, irreducibility of the group representation
implies irreducibility of the Lie module.  This isolates the integration
content from the order-theoretic argument. -/
theorem lieModule_isIrreducible_of_group_stable
    {G L V : Type*} [Group G] [LieRing L]
    [AddCommGroup V] [Module ℂ V] [LieRingModule L V]
    (rho : Representation ℂ G V)
    [Representation.IsIrreducible rho]
    (hStable : ∀ (N : LieSubmodule ℂ L V) (g : G) {v : V},
      v ∈ N → rho g v ∈ N) :
    LieModule.IsIrreducible ℂ L V := by
  let : IsSimpleModule ℂ[G] rho.asModule := inferInstance
  let : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] rho.asModule
  apply LieModule.IsIrreducible.mk
  intro N hN
  let S : Subrepresentation rho :=
    { toSubmodule := (N : Submodule ℂ V)
      apply_mem_toSubmodule := fun g _v hv => hStable N g hv }
  rcases IsSimpleOrder.eq_bot_or_eq_top S with hBot | hTop
  · exfalso
    apply hN
    apply LieSubmodule.ext
    intro v
    change v ∈ S ↔ v ∈ (⊥ : Subrepresentation rho)
    rw [hBot]
  · apply LieSubmodule.ext
    intro v
    change v ∈ S ↔ v ∈ (⊤ : Subrepresentation rho)
    rw [hTop]

/-!
## `SU(2)` certificate
-/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The finite output needed from the highest-weight classification of one
irreducible `SU(2)` representation.  The center formula is deliberately not a
field: it is derived from the certified highest-weight vector. -/
structure SU2HighestWeightCertificate
    (rho : Representation ℂ SU2 V) where
  highestWeight : ℕ
  highestWeightVector : V
  highestWeightVector_ne_zero : highestWeightVector ≠ 0
  center_eigenvalue :
    rho su2CenterElement highestWeightVector =
      ((-1 : ℂ) ^ highestWeight) • highestWeightVector
  dimension_formula : Module.finrank ℂ V = highestWeight + 1
  trivial_action_of_highestWeight_eq_zero :
    highestWeight = 0 → ∀ g, rho g = LinearMap.id

namespace SU2HighestWeightCertificate

variable [FiniteDimensional ℂ V]
variable {rho : Representation ℂ SU2 V}

/-- Schur's lemma upgrades the highest-weight-vector center calculation to an
operator identity on the full irreducible representation. -/
theorem center_action (C : SU2HighestWeightCertificate rho)
    [Representation.IsIrreducible rho] :
    rho su2CenterElement =
      ((-1 : ℂ) ^ C.highestWeight) •
        (LinearMap.id : V →ₗ[ℂ] V) := by
  apply central_action_eq_smul_id_of_eigenvector
    (rho := rho) (z := su2CenterElement)
    (a := (-1 : ℂ) ^ C.highestWeight)
    (v := C.highestWeightVector)
  · rw [Submonoid.mem_center_iff]
    exact fun g => (su2CenterElement_central g).symm
  · exact C.highestWeightVector_ne_zero
  · exact C.center_eigenvalue

omit [FiniteDimensional ℂ V] in
theorem classify_of_dimension_le_six
    (C : SU2HighestWeightCertificate rho)
    (hDim : Module.finrank ℂ V ≤ 6) :
    (C.highestWeight = 0 ∧ Module.finrank ℂ V = 1) ∨
    (C.highestWeight = 1 ∧ Module.finrank ℂ V = 2) ∨
    (C.highestWeight = 2 ∧ Module.finrank ℂ V = 3) ∨
    (C.highestWeight = 3 ∧ Module.finrank ℂ V = 4) ∨
    (C.highestWeight = 4 ∧ Module.finrank ℂ V = 5) ∨
    (C.highestWeight = 5 ∧ Module.finrank ℂ V = 6) := by
  exact su2_highestWeight_of_dimension_le_six
    C.highestWeight (Module.finrank ℂ V) C.dimension_formula hDim

omit [FiniteDimensional ℂ V] in
theorem center_exponent_eq_dimension_sub_one
    (C : SU2HighestWeightCertificate rho) :
    C.highestWeight = Module.finrank ℂ V - 1 :=
  su2_center_exponent_eq_dimension_sub_one
    C.highestWeight (Module.finrank ℂ V) C.dimension_formula

omit [FiniteDimensional ℂ V] in
/-- The one-dimensional highest-weight-zero irreducible is the trivial
representation at the level of its action operators. -/
theorem action_eq_id_of_finrank_eq_one
    (C : SU2HighestWeightCertificate rho)
    (hDimension : Module.finrank ℂ V = 1) :
    ∀ g, rho g = LinearMap.id := by
  apply C.trivial_action_of_highestWeight_eq_zero
  have hFormula := C.dimension_formula
  omega

end SU2HighestWeightCertificate

/-!
## Lie-algebra construction of the `SU(2)` certificate
-/

universe u v

/-- The remaining group-to-Lie data needed to construct an `SU(2)`
highest-weight certificate.  The dimension formula is not included: it is
derived from the irreducible `sl₂` lowering string. -/
structure SU2LieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V) where
  L : Type v
  [lieRing : LieRing L]
  [lieAlgebra : LieAlgebra ℂ L]
  [lieRingModule : LieRingModule L V]
  [lieModule : LieModule ℂ L V]
  h : L
  e : L
  f : L
  triple : IsSl2Triple h e f
  spans : triple.toLieSubalgebra ℂ = ⊤
  irreducible : LieModule.IsIrreducible ℂ L V
  center_eigenvalue :
    ∀ {n : ℕ} {v : V}, triple.HasPrimitiveVectorWith v (n : ℂ) →
      rho su2CenterElement v = ((-1 : ℂ) ^ n) • v
  one_dimensional_trivial :
    Module.finrank ℂ V = 1 → ∀ g, rho g = LinearMap.id

attribute [instance] SU2LieModel.lieRing SU2LieModel.lieAlgebra
  SU2LieModel.lieRingModule SU2LieModel.lieModule

namespace SU2LieModel

/-- Mathlib's primitive-vector existence theorem and the checked lowering
string argument construct the complete `SU(2)` highest-weight certificate
from the differentiated Lie model. -/
theorem toHighestWeightCertificate
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    [FiniteDimensional ℂ V]
    (S : SU2LieModel rho) :
    Nonempty (SU2HighestWeightCertificate rho) := by
  let : LieModule.IsIrreducible ℂ S.L V := S.irreducible
  obtain ⟨n, v, P, hDimension⟩ :=
    Sl2String.exists_highestWeight_and_dimension
      (L := S.L) (M := V) S.triple S.spans
  exact ⟨
    { highestWeight := n
      highestWeightVector := v
      highestWeightVector_ne_zero := P.ne_zero
      center_eigenvalue := S.center_eigenvalue P
      dimension_formula := hDimension
      trivial_action_of_highestWeight_eq_zero := by
        intro hn
        apply S.one_dimensional_trivial
        omega }⟩

end SU2LieModel

/-!
## The fixed standard `sl₂(ℂ)` model
-/

/-- The remaining representation-dependent data after fixing the acting Lie
algebra to the standard trace-zero two-by-two complex matrices.  The standard
`sl₂` triple and the fact that it spans the acting algebra are theorems in
`StandardSl2`, rather than fields of this certificate. -/
structure SU2StandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V) where
  [lieRingModule : LieRingModule StandardSl2.Algebra V]
  [lieModule : LieModule ℂ StandardSl2.Algebra V]
  irreducible : LieModule.IsIrreducible ℂ StandardSl2.Algebra V
  center_eigenvalue :
    ∀ {n : ℕ} {v : V},
      StandardSl2.isSl2Triple.HasPrimitiveVectorWith v (n : ℂ) →
        rho su2CenterElement v = ((-1 : ℂ) ^ n) • v
  trivial_action_of_zero_differential :
    (∀ X : StandardSl2.Algebra, ∀ v : V, ⁅X, v⁆ = 0) →
      ∀ g, rho g = LinearMap.id

namespace SU2StandardLieModel

/-- Package the fixed standard matrix Lie algebra as the generic Lie model
consumed by the lowering-string theorem. -/
def toLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    [FiniteDimensional ℂ V]
    (S : SU2StandardLieModel rho) :
    SU2LieModel rho := by
  letI : LieRingModule StandardSl2.Algebra V := S.lieRingModule
  letI : LieModule ℂ StandardSl2.Algebra V := S.lieModule
  exact
    { L := StandardSl2.Algebra
      lieRing := inferInstance
      lieAlgebra := inferInstance
      lieRingModule := inferInstance
      lieModule := inferInstance
      h := StandardSl2.H
      e := StandardSl2.E
      f := StandardSl2.F
      triple := StandardSl2.isSl2Triple
      spans := StandardSl2.toLieSubalgebra_eq_top
      irreducible := S.irreducible
      center_eigenvalue := S.center_eigenvalue
      one_dimensional_trivial := by
        intro hDimension
        apply S.trivial_action_of_zero_differential
        exact StandardSl2.action_eq_zero_of_finrank_eq_one hDimension }

/-- The checked standard `sl₂` matrix calculation and lowering-string theorem
produce the complete SU(2) certificate from the remaining differentiated
representation data. -/
theorem toHighestWeightCertificate
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    [FiniteDimensional ℂ V]
    (S : SU2StandardLieModel rho) :
    Nonempty (SU2HighestWeightCertificate rho) :=
  S.toLieModel.toHighestWeightCertificate

end SU2StandardLieModel

/-!
## The fixed standard `sl₃(ℂ)` model
-/

/-- The representation-dependent data needed after fixing the acting Lie
algebra to the standard trace-zero three-by-three complex matrices.  The
low-dimensional highest-weight classification is now checked internally;
the remaining analytic input is differentiation of the group action and the
integration statement saying that zero differential gives the trivial
connected-group action. -/
structure SU3StandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) where
  [lieRingModule : LieRingModule StandardSl3.Algebra V]
  [lieModule : LieModule ℂ StandardSl3.Algebra V]
  irreducible : LieModule.IsIrreducible ℂ StandardSl3.Algebra V
  trivial_action_of_zero_differential :
    (∀ X : StandardSl3.Algebra, ∀ v : V, ⁅X, v⁆ = 0) →
      ∀ g, rho g = LinearMap.id

namespace SU3StandardLieModel

/-- The checked concrete `sl₃(ℂ)` highest-weight argument gives exactly the
color-factor dimension list used by semisimple embedding classification. -/
theorem finrank_eq_one_or_three_or_six
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU3 V}
    [FiniteDimensional ℂ V]
    (S : SU3StandardLieModel rho)
    (hDimension : Module.finrank ℂ V ≤ 6) :
    Module.finrank ℂ V = 1 ∨ Module.finrank ℂ V = 3 ∨
      Module.finrank ℂ V = 6 := by
  let : LieRingModule StandardSl3.Algebra V := S.lieRingModule
  let : LieModule ℂ StandardSl3.Algebra V := S.lieModule
  let : LieModule.IsIrreducible ℂ StandardSl3.Algebra V := S.irreducible
  exact Sl3HighestWeight.finrank_eq_one_or_three_or_six hDimension

/-- A one-dimensional standard `sl₃(ℂ)` module has zero differential, so the
model's integration bridge makes the corresponding `SU(3)` action trivial. -/
theorem action_eq_id_of_finrank_eq_one
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU3 V}
    [FiniteDimensional ℂ V]
    (S : SU3StandardLieModel rho)
    (hDimension : Module.finrank ℂ V = 1) :
    ∀ g, rho g = LinearMap.id := by
  let : LieRingModule StandardSl3.Algebra V := S.lieRingModule
  let : LieModule ℂ StandardSl3.Algebra V := S.lieModule
  apply S.trivial_action_of_zero_differential
  exact StandardSl3.action_eq_zero_of_finrank_eq_one hDimension

end SU3StandardLieModel

/-!
## Integrated standard Lie models
-/

/-- A differentiated `SU(2)` model before Lie irreducibility is inferred.
The `lieSubmodule_group_stable` field is the precise integration statement
needed to derive it from irreducibility of the original group action. -/
structure SU2IntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V) where
  [lieRingModule : LieRingModule StandardSl2.Algebra V]
  [lieModule : LieModule ℂ StandardSl2.Algebra V]
  lieSubmodule_group_stable :
    ∀ (N : LieSubmodule ℂ StandardSl2.Algebra V) (g : SU2) {v : V},
      v ∈ N → rho g v ∈ N
  center_eigenvalue :
    ∀ {n : ℕ} {v : V},
      StandardSl2.isSl2Triple.HasPrimitiveVectorWith v (n : ℂ) →
        rho su2CenterElement v = ((-1 : ℂ) ^ n) • v
  trivial_action_of_zero_differential :
    (∀ X : StandardSl2.Algebra, ∀ v : V, ⁅X, v⁆ = 0) →
      ∀ g, rho g = LinearMap.id

namespace SU2IntegratedStandardLieModel

/-- Group irreducibility plus integration-stability supplies the old standard
Lie model interface without separately assuming Lie irreducibility. -/
def toStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    [Representation.IsIrreducible rho]
    (S : SU2IntegratedStandardLieModel rho) :
    SU2StandardLieModel rho := by
  letI : LieRingModule StandardSl2.Algebra V := S.lieRingModule
  letI : LieModule ℂ StandardSl2.Algebra V := S.lieModule
  exact
    { lieRingModule := inferInstance
      lieModule := inferInstance
      irreducible := lieModule_isIrreducible_of_group_stable
        rho S.lieSubmodule_group_stable
      center_eigenvalue := S.center_eigenvalue
      trivial_action_of_zero_differential :=
        S.trivial_action_of_zero_differential }

end SU2IntegratedStandardLieModel

/-- The analogous differentiated `SU(3)` model.  The low-dimensional
highest-weight classification is already internal; only integration of Lie
submodules and zero differential remains representation-dependent. -/
structure SU3IntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) where
  [lieRingModule : LieRingModule StandardSl3.Algebra V]
  [lieModule : LieModule ℂ StandardSl3.Algebra V]
  lieSubmodule_group_stable :
    ∀ (N : LieSubmodule ℂ StandardSl3.Algebra V) (g : SU3) {v : V},
      v ∈ N → rho g v ∈ N
  trivial_action_of_zero_differential :
    (∀ X : StandardSl3.Algebra, ∀ v : V, ⁅X, v⁆ = 0) →
      ∀ g, rho g = LinearMap.id

namespace SU3IntegratedStandardLieModel

def toStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU3 V}
    [Representation.IsIrreducible rho]
    (S : SU3IntegratedStandardLieModel rho) :
    SU3StandardLieModel rho := by
  letI : LieRingModule StandardSl3.Algebra V := S.lieRingModule
  letI : LieModule ℂ StandardSl3.Algebra V := S.lieModule
  exact
    { lieRingModule := inferInstance
      lieModule := inferInstance
      irreducible := lieModule_isIrreducible_of_group_stable
        rho S.lieSubmodule_group_stable
      trivial_action_of_zero_differential :=
        S.trivial_action_of_zero_differential }

end SU3IntegratedStandardLieModel

/-!
## Exponentially integrated standard Lie models
-/

/-- The standard complexified Lie-algebra element whose compact-real-form
exponential is the nontrivial center element of `SU(2)`. -/
def su2CenterLieElement : StandardSl2.Algebra :=
  ((Real.pi : ℂ) * Complex.I) • StandardSl2.H

/-- Once the represented `SU(2)` center agrees with the exponential of
`pi * I * H`, its action on a primitive vector is the expected parity sign. -/
theorem su2_center_eigenvalue_of_exponential
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    [LieRingModule StandardSl2.Algebra V]
    [LieModule ℂ StandardSl2.Algebra V]
    (rho : Representation ℂ SU2 V)
    (hCenter :
      rho su2CenterElement =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl2.Algebra V su2CenterLieElement)) :
    ∀ {n : ℕ} {v : V},
      StandardSl2.isSl2Triple.HasPrimitiveVectorWith v (n : ℂ) →
        rho su2CenterElement v = ((-1 : ℂ) ^ n) • v := by
  intro n v P
  rw [hCenter]
  have hEigen :
      LieModule.toEnd ℂ StandardSl2.Algebra V su2CenterLieElement v =
        ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) • v := by
    change ⁅su2CenterLieElement, v⁆ = _
    rw [su2CenterLieElement, smul_lie, P.lie_h, smul_smul]
    congr 1
    ring
  rw [finiteDimensionalExponential_apply_of_apply_eq_smul _ hEigen]
  congr 1
  rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- An `SU(2)` differentiated model whose global integration data is reduced
to a finite-product family of exponential generators and the usual
representation/exponential compatibility on that family. -/
structure SU2ExponentiallyIntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V) where
  [finiteDimensional : FiniteDimensional ℂ V]
  [lieRingModule : LieRingModule StandardSl2.Algebra V]
  [lieModule : LieModule ℂ StandardSl2.Algebra V]
  parameter : Type
  generation : FiniteProductGeneration SU2 parameter
  toComplexLie : parameter → StandardSl2.Algebra
  action_generator :
    ∀ x : parameter,
      rho (generation.generator x) =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl2.Algebra V (toComplexLie x))
  center_eigenvalue :
    ∀ {n : ℕ} {v : V},
      StandardSl2.isSl2Triple.HasPrimitiveVectorWith v (n : ℂ) →
        rho su2CenterElement v = ((-1 : ℂ) ^ n) • v

namespace SU2ExponentiallyIntegratedStandardLieModel

/-- The operator-exponential and finite-product lemmas construct both global
integration fields of `SU2IntegratedStandardLieModel`. -/
def toIntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    (S : SU2ExponentiallyIntegratedStandardLieModel rho) :
    SU2IntegratedStandardLieModel rho := by
  letI : FiniteDimensional ℂ V := S.finiteDimensional
  letI : LieRingModule StandardSl2.Algebra V := S.lieRingModule
  letI : LieModule ℂ StandardSl2.Algebra V := S.lieModule
  exact
    { lieRingModule := inferInstance
      lieModule := inferInstance
      lieSubmodule_group_stable :=
        lieSubmodule_group_stable_of_finiteDimensionalExponential
          rho S.generation S.toComplexLie S.action_generator
      center_eigenvalue := S.center_eigenvalue
      trivial_action_of_zero_differential :=
        action_eq_id_of_finiteDimensionalExponential_of_lieAction_eq_zero
          rho S.generation S.toComplexLie S.action_generator }

end SU2ExponentiallyIntegratedStandardLieModel

/-- A sharper `SU(2)` exponential model in which the center formula is not
supplied separately: the generating family contains `pi * I * H`, so the
formula follows from the checked eigenvector-exponential theorem. -/
structure SU2GeneratedExponentialStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU2 V) where
  [finiteDimensional : FiniteDimensional ℂ V]
  [lieRingModule : LieRingModule StandardSl2.Algebra V]
  [lieModule : LieModule ℂ StandardSl2.Algebra V]
  parameter : Type
  generation : FiniteProductGeneration SU2 parameter
  toComplexLie : parameter → StandardSl2.Algebra
  action_generator :
    ∀ x : parameter,
      rho (generation.generator x) =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl2.Algebra V (toComplexLie x))
  centerParameter : parameter
  center_generator :
    generation.generator centerParameter = su2CenterElement
  center_lie : toComplexLie centerParameter = su2CenterLieElement

namespace SU2GeneratedExponentialStandardLieModel

/-- Forgetting the distinguished center parameter derives the older
exponential model, including its center-eigenvalue field. -/
def toExponentiallyIntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    (S : SU2GeneratedExponentialStandardLieModel rho) :
    SU2ExponentiallyIntegratedStandardLieModel rho := by
  letI : FiniteDimensional ℂ V := S.finiteDimensional
  letI : LieRingModule StandardSl2.Algebra V := S.lieRingModule
  letI : LieModule ℂ StandardSl2.Algebra V := S.lieModule
  have hCenter :
      rho su2CenterElement =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl2.Algebra V su2CenterLieElement) := by
    rw [← S.center_generator, ← S.center_lie]
    exact S.action_generator S.centerParameter
  exact
    { finiteDimensional := inferInstance
      lieRingModule := inferInstance
      lieModule := inferInstance
      parameter := S.parameter
      generation := S.generation
      toComplexLie := S.toComplexLie
      action_generator := S.action_generator
      center_eigenvalue := su2_center_eigenvalue_of_exponential rho hCenter }

def toIntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU2 V}
    (S : SU2GeneratedExponentialStandardLieModel rho) :
    SU2IntegratedStandardLieModel rho :=
  S.toExponentiallyIntegratedStandardLieModel.toIntegratedStandardLieModel

end SU2GeneratedExponentialStandardLieModel

/-- The analogous exponentially integrated `SU(3)` model. -/
structure SU3ExponentiallyIntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ SU3 V) where
  [finiteDimensional : FiniteDimensional ℂ V]
  [lieRingModule : LieRingModule StandardSl3.Algebra V]
  [lieModule : LieModule ℂ StandardSl3.Algebra V]
  parameter : Type
  generation : FiniteProductGeneration SU3 parameter
  toComplexLie : parameter → StandardSl3.Algebra
  action_generator :
    ∀ x : parameter,
      rho (generation.generator x) =
        finiteDimensionalExponential
          (LieModule.toEnd ℂ StandardSl3.Algebra V (toComplexLie x))

namespace SU3ExponentiallyIntegratedStandardLieModel

def toIntegratedStandardLieModel
    {V : Type u} [AddCommGroup V] [Module ℂ V]
    {rho : Representation ℂ SU3 V}
    (S : SU3ExponentiallyIntegratedStandardLieModel rho) :
    SU3IntegratedStandardLieModel rho := by
  letI : FiniteDimensional ℂ V := S.finiteDimensional
  letI : LieRingModule StandardSl3.Algebra V := S.lieRingModule
  letI : LieModule ℂ StandardSl3.Algebra V := S.lieModule
  exact
    { lieRingModule := inferInstance
      lieModule := inferInstance
      lieSubmodule_group_stable :=
        lieSubmodule_group_stable_of_finiteDimensionalExponential
          rho S.generation S.toComplexLie S.action_generator
      trivial_action_of_zero_differential :=
        action_eq_id_of_finiteDimensionalExponential_of_lieAction_eq_zero
          rho S.generation S.toComplexLie S.action_generator }

end SU3ExponentiallyIntegratedStandardLieModel

/-!
## `SU(3)` certificate
-/

/-- The finite output needed from the highest-weight classification of one
irreducible `SU(3)` representation. -/
structure SU3HighestWeightCertificate
    (rho : Representation ℂ SU3 V) where
  firstWeight : ℕ
  secondWeight : ℕ
  dimension_formula :
    2 * Module.finrank ℂ V = SU3TwiceDimension firstWeight secondWeight
  trivial_action_of_highestWeights_eq_zero :
    firstWeight = 0 → secondWeight = 0 → ∀ g, rho g = LinearMap.id

namespace SU3HighestWeightCertificate

variable {rho : Representation ℂ SU3 V}

theorem classify_of_dimension_le_six
    (C : SU3HighestWeightCertificate rho)
    (hDim : Module.finrank ℂ V ≤ 6) :
    (C.firstWeight = 0 ∧ C.secondWeight = 0 ∧ Module.finrank ℂ V = 1) ∨
    (C.firstWeight = 1 ∧ C.secondWeight = 0 ∧ Module.finrank ℂ V = 3) ∨
    (C.firstWeight = 0 ∧ C.secondWeight = 1 ∧ Module.finrank ℂ V = 3) ∨
    (C.firstWeight = 2 ∧ C.secondWeight = 0 ∧ Module.finrank ℂ V = 6) ∨
    (C.firstWeight = 0 ∧ C.secondWeight = 2 ∧ Module.finrank ℂ V = 6) := by
  exact su3_highestWeight_of_dimension_le_six
    C.firstWeight C.secondWeight (Module.finrank ℂ V)
    C.dimension_formula hDim

/-- The one-dimensional `(0,0)` irreducible is the trivial representation at
the level of its action operators. -/
theorem action_eq_id_of_finrank_eq_one
    (C : SU3HighestWeightCertificate rho)
    (hDimension : Module.finrank ℂ V = 1) :
    ∀ g, rho g = LinearMap.id := by
  have hClassified := C.classify_of_dimension_le_six (by omega)
  rcases hClassified with h | h | h | h | h
  · exact C.trivial_action_of_highestWeights_eq_zero h.1 h.2.1
  · omega
  · omega
  · omega
  · omega

end SU3HighestWeightCertificate

end


end HighestWeightBridge
end GUT
