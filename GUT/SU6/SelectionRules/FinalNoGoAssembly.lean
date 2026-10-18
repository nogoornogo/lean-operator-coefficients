import GUT.SU6.Hypercharge.HyperchargeBranchArithmetic
import GUT.SU6.Characters.NormalizedLaurent
import GUT.SU6.Embeddings.ContinuousEmbeddingRegularityBridge
import GUT.SU6.SelectionRules.StandardBranch.PhysicalChargeResolvedBridge
import GUT.SU6.SelectionRules.Models.PhysicalMassSpectrumBridge
import GUT.SU6.Characters.PhysicalTorusCharacterBridge
import GUT.SU6.SelectionRules.StandardBranch.StandardAbelianProtection

open Math

/-!
# Conditional assembly of the ordinary-Abelian no-go argument

This file composes the already checked branchwise results without claiming
that every physical `SU(6)` model supplies their source certificates.

* Hypercharge arithmetic reduces an injective oriented physical circle to the
  flipped or standard pair.
* The flipped restricted-character certificate contradicts the ambient
  `swap36` obstruction.
* The remaining standard certificate feeds the charge-resolved standard charge-orbit bridge source
  theorem into the Abelian proton-operator neutrality proton-operator calculation.

An alternative assembly below uses the hypercharge character rigidity physical-torus character theorem to
select the standard pair directly.  It does not use the flipped obstruction,
which remains a logically independent result.

The exact chiral-spectrum identifications remain explicit inputs.  The main
selection-rule conclusion constructs a supported, gauge- and Lorentz-invariant
dimension-six local operator with trivial residual character; it does not
assume that its Wilson coefficient or decay amplitude is nonzero.  The older
present-channel result is retained only as a stronger conditional corollary.
No continuous `U(1)` anomaly equation is used here.
-/

namespace GUT

noncomputable section

universe u

namespace FinalNoGoAssembly

open ActualBlockCentralizer
open ActualCompactCentralizer
open CompactEmbeddingClassification
open ContinuousEmbeddingRegularityBridge
open FiniteAbelianChargeSectors
open HyperchargeBranchArithmetic
open PhysicalChargeResolvedBridge
open PhysicalMassSpectrumBridge
open SmoothEmbeddingBridge
open StandardAbelianProtection
open StandardBlockChargeProjection
open StandardBlockGaugeCancellation
open StandardBranchProtonObstruction
open StandardModelLocalOperator
open StandardPhysicalSpectrumBridge

/-- Total virtual multiplicity of gauge singlets after forgetting their
residual Abelian charge labels. -/
def totalSingletIndex
    {H : Type u} [CommGroup H]
    (singlets : ChargeLabel H →₀ ℤ) : ℤ :=
  singlets.sum fun _ multiplicity => multiplicity

/-!
## semisimple embedding classification geometry from continuous compact matrix embeddings
-/

/-- The physical semisimple embedding classification geometry with only continuity, injectivity, and a faithful
commuting hypercharge circle as source assumptions. -/
structure ContinuousHyperchargeEmbedding where
  iota : ProductGroup →ₜ* CompactEmbeddingClassification.SU6
  embedding_injective : Function.Injective iota
  hypercharge : Circle →ₜ* CompactEmbeddingClassification.SU6
  hypercharge_injective : Function.Injective hypercharge
  hypercharge_commutes :
    ∀ z g, hypercharge z * iota g = iota g * hypercharge z

/-- An injective `SU(3) x SU(2)` matrix embedding together with its actual
injective hypercharge circle.  The only analytic input is ordinary Frechet
differentiability at zero in the canonical source exponential coordinates.

This structure contains no representation-classification certificate.  The
checked smooth semisimple embedding classification bridge constructs that certificate below. -/
structure MatrixDifferentiableHyperchargeEmbedding where
  iota : ProductGroup →ₜ* CompactEmbeddingClassification.SU6
  embedding_injective : Function.Injective iota
  hypercharge : Circle →ₜ* CompactEmbeddingClassification.SU6
  hypercharge_injective : Function.Injective hypercharge
  hypercharge_commutes :
    ∀ z g, hypercharge z * iota g = iota g * hypercharge z
  exponentialChart_differentiableAt :
    DifferentiableAt ℝ
      (exponentialChartMap
        (iota : ProductGroup →* CompactEmbeddingClassification.SU6)) 0

namespace MatrixDifferentiableHyperchargeEmbedding

/-- An injective circle homomorphism is nontrivial. -/
theorem hypercharge_ne_one
    (G : MatrixDifferentiableHyperchargeEmbedding) :
    G.hypercharge ≠ 1 := by
  intro hOne
  have hImages : G.hypercharge (-1 : Circle) = G.hypercharge 1 := by
    rw [hOne]
    simp
  have hPoints := G.hypercharge_injective hImages
  have hCoe := congrArg (fun z : Circle => (z : ℂ)) hPoints
  norm_num at hCoe

/-- The classified `3+2+1` decomposition constructed from the actual
differentiable embedding and commuting hypercharge circle. -/
noncomputable def weakDoubletData
    (G : MatrixDifferentiableHyperchargeEmbedding) :
    WeakDoubletData
      (euclideanDefiningRestriction
        (G.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)) :=
  Classical.choice
    (SmoothEmbeddingBridge.injectiveEmbedding_with_hypercharge_has_classifiedWeakDoubletDecomposition_of_exponentialChartDifferentiableAt
      G.iota G.embedding_injective G.hypercharge
      G.hypercharge_commutes G.hypercharge_ne_one
      G.exponentialChart_differentiableAt)

/-- The supplied hypercharge circle takes values in the physical
centralizer. -/
theorem hypercharge_mem_physicalCentralizer
    (G : MatrixDifferentiableHyperchargeEmbedding) (z : Circle) :
    G.hypercharge z ∈ PhysicalCentralizer
      (G.iota : ProductGroup →*
        CompactEmbeddingClassification.SU6) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨g, rfl⟩ := hg
  exact (G.hypercharge_commutes z g).symm

/-- Corestrict the actual hypercharge circle to the checked physical
centralizer. -/
def centralizerCircle
    (G : MatrixDifferentiableHyperchargeEmbedding) :
    Circle →ₜ* PhysicalCentralizer
      (G.iota : ProductGroup →*
        CompactEmbeddingClassification.SU6) where
  toMonoidHom :=
    { toFun := fun z =>
        ⟨G.hypercharge z, G.hypercharge_mem_physicalCentralizer z⟩
      map_one' := Subtype.ext (map_one G.hypercharge)
      map_mul' := fun z w => Subtype.ext (map_mul G.hypercharge z w) }
  continuous_toFun :=
    G.hypercharge.continuous.subtype_mk
      G.hypercharge_mem_physicalCentralizer

/-- The unique integer cocharacter pair of the actual hypercharge circle in
the semisimple embedding classification block coordinates. -/
noncomputable def hyperchargePair
    (G : MatrixDifferentiableHyperchargeEmbedding) : ℤ × ℤ :=
  Classical.choose
    (existsUnique_eq_physicalCircleHom
      (G.iota : ProductGroup →*
        CompactEmbeddingClassification.SU6) G.weakDoubletData
      G.centralizerCircle).exists

/-- The extracted integer pair reconstructs the actual centralizer-valued
hypercharge circle. -/
theorem centralizerCircle_eq_physicalCircleHom
    (G : MatrixDifferentiableHyperchargeEmbedding) :
    G.centralizerCircle =
      physicalCircleHom (G.iota : ProductGroup →*
        CompactEmbeddingClassification.SU6)
        G.weakDoubletData G.hyperchargePair :=
  Classical.choose_spec
    (existsUnique_eq_physicalCircleHom
      (G.iota : ProductGroup →*
        CompactEmbeddingClassification.SU6) G.weakDoubletData
      G.centralizerCircle).exists

/-- Pointwise reconstruction of the original `SU(6)`-valued hypercharge
circle from its unique integer cocharacter pair. -/
theorem hypercharge_eq_physicalCircleHom_val
    (G : MatrixDifferentiableHyperchargeEmbedding) (z : Circle) :
    G.hypercharge z =
      (physicalCircleHom (G.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        G.weakDoubletData G.hyperchargePair z :
          CompactEmbeddingClassification.SU6) := by
  have hAtZ := DFunLike.congr_fun
    G.centralizerCircle_eq_physicalCircleHom z
  exact congrArg Subtype.val hAtZ

/-- Faithfulness of the actual hypercharge circle transports to the extracted
integer-coordinate circle. -/
theorem physicalCircleHom_injective
    (G : MatrixDifferentiableHyperchargeEmbedding) :
    Function.Injective
      (physicalCircleHom (G.iota : ProductGroup →*
        CompactEmbeddingClassification.SU6)
        G.weakDoubletData G.hyperchargePair) := by
  rw [← G.centralizerCircle_eq_physicalCircleHom]
  intro z w h
  apply G.hypercharge_injective
  exact congrArg Subtype.val h

/-- The integer pair of an injective physical hypercharge circle is
primitive. -/
theorem hyperchargePair_primitive
    (G : MatrixDifferentiableHyperchargeEmbedding) :
    G.hyperchargePair.1.gcd G.hyperchargePair.2 = 1 :=
  (ActualCompactCentralizer.physicalCircleHom_injective_iff
    (G.iota : ProductGroup →*
      CompactEmbeddingClassification.SU6)
    G.weakDoubletData G.hyperchargePair).mp
      G.physicalCircleHom_injective

/-- Continuity of a compact matrix-group homomorphism automatically supplies
the differentiability field of the original E geometry interface. -/
def ofContinuous
    (iota : ProductGroup →ₜ* CompactEmbeddingClassification.SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* CompactEmbeddingClassification.SU6)
    (hYInjective : Function.Injective Y)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z) :
    MatrixDifferentiableHyperchargeEmbedding where
  iota := iota
  embedding_injective := hInjective
  hypercharge := Y
  hypercharge_injective := hYInjective
  hypercharge_commutes := hCommute
  exponentialChart_differentiableAt :=
    ContinuousEmbeddingRegularityBridge.exponentialChartMap_differentiableAt
      iota

/-- Build the geometric source from the ambient differentiability interface
used by concrete matrix-algebraic embeddings. -/
def ofAmbientlyDifferentiable
    (iota : ProductGroup →ₜ* CompactEmbeddingClassification.SU6)
    (hInjective : Function.Injective iota)
    (Y : Circle →ₜ* CompactEmbeddingClassification.SU6)
    (hYInjective : Function.Injective Y)
    (hCommute : ∀ z g, Y z * iota g = iota g * Y z)
    (D : AmbientlyDifferentiableEmbedding
      (iota : ProductGroup →*
        CompactEmbeddingClassification.SU6)) :
    MatrixDifferentiableHyperchargeEmbedding where
  iota := iota
  embedding_injective := hInjective
  hypercharge := Y
  hypercharge_injective := hYInjective
  hypercharge_commutes := hCommute
  exponentialChart_differentiableAt :=
    D.toExponentialChartDifferentiableEmbedding.hasFDerivAt_zero.differentiableAt

end MatrixDifferentiableHyperchargeEmbedding

namespace ContinuousHyperchargeEmbedding

/-- Automatic regularity converts the continuity-only physical geometry to
the original differentiable scoped interface. -/
noncomputable def toMatrixDifferentiable
    (G : ContinuousHyperchargeEmbedding) :
    MatrixDifferentiableHyperchargeEmbedding :=
  MatrixDifferentiableHyperchargeEmbedding.ofContinuous
    G.iota G.embedding_injective G.hypercharge G.hypercharge_injective
    G.hypercharge_commutes

/-- The checked semisimple embedding classification decomposition attached canonically to continuity-only
geometry. -/
noncomputable abbrev weakDoubletData
    (G : ContinuousHyperchargeEmbedding) :=
  G.toMatrixDifferentiable.weakDoubletData

/-- The checked integral hypercharge cocharacter attached to continuity-only
geometry. -/
noncomputable abbrev hyperchargePair
    (G : ContinuousHyperchargeEmbedding) :=
  G.toMatrixDifferentiable.hyperchargePair

end ContinuousHyperchargeEmbedding

/-- Explicit source data needed to compose the checked standard and flipped
branches.

This is a conditional assembly interface, not yet a theorem that every
physical `SU(6)` model produces such data.  In particular, `standardSpectrum`
and `flippedSpectrum` expose the two remaining branch-specific physical
source identifications. -/
structure OrdinaryAbelianBranchSource
    (H : Type u) [CommGroup H] where
  iota : ProductGroup →* CompactEmbeddingClassification.SU6
  weakDoubletData : WeakDoubletData (euclideanDefiningRestriction iota)
  hyperchargePair : ℤ × ℤ
  hypercharge_injective :
    Function.Injective
      (physicalCircleHom iota weakDoubletData hyperchargePair)
  hypercharge_oriented_neutrality :
    (hyperchargePair.2 = 0 ∧ 0 < hyperchargePair.1) ∨
      (singletExponent hyperchargePair = 0 ∧ 0 < hyperchargePair.2)
  matter : OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  standardSpectrum :
    hyperchargePair = standardPair →
      IsExactSMOnlyCoefficientSpectrum
        (ordinaryAbelianResolvedCharacter iota weakDoubletData matter)
        generations physicalCharges singlets
  flippedSpectrum :
    hyperchargePair = flippedPair →
      ∀ t : NormalizedVirtualRestriction.DiagonalSU6Point,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            matter.toFiniteVirtual t =
          NormalizedVirtualRestriction.diagonalLaurentEval
            (Flipped.Normalized.zscale generations
                Flipped.Normalized.flippedSMCharacter +
              Flipped.Normalized.singletCharacter
                (totalSingletIndex singlets)) t

namespace OrdinaryAbelianBranchSource

variable {H : Type u} [CommGroup H]

/-- The supplied flipped physical spectrum is incompatible with restriction
of the underlying finite virtual `SU(6)` representation.  This is the D
obstruction, logically separate from standard charge-orbit bridge and Abelian proton-operator neutrality. -/
theorem flippedSpectrum_false
    (S : OrdinaryAbelianBranchSource H)
    (hFlipped : S.hyperchargePair = flippedPair) : False := by
  exact
    NormalizedVirtualRestriction.FiniteVirtualSU6Representation.no_restrictedCharacter_eq_nonzero_generation_add_singlets_eval
      S.generations S.generations_ne (totalSingletIndex S.singlets)
      ⟨S.matter.toFiniteVirtual, S.flippedSpectrum hFlipped⟩

/-- The actual injective oriented hypercharge circle is therefore the
standard pair once the flipped character obstruction is imposed. -/
theorem hyperchargePair_eq_standard
    (S : OrdinaryAbelianBranchSource H) :
    S.hyperchargePair = standardPair := by
  rcases
      physicalCircleHom_eq_flipped_or_standard_of_injective_of_oriented_neutrality
        S.iota S.weakDoubletData S.hyperchargePair
        S.hypercharge_injective S.hypercharge_oriented_neutrality with
    hFlipped | hStandard
  · exact (S.flippedSpectrum_false hFlipped).elim
  · exact hStandard

/-- Package the surviving standard-branch data into the strict ordinary
Abelian standard charge-orbit bridge source interface. -/
def toStandardProjectedSource
    (S : OrdinaryAbelianBranchSource H) :
    PureSMOrdinaryAbelianProjectedSource H where
  iota := S.iota
  weakDoubletData := S.weakDoubletData
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  spectrum := S.standardSpectrum S.hyperchargePair_eq_standard

/-- Positive local-operator form of the conditional scoped assembly. After the flipped branch
selects the standard branch, standard charge-orbit bridge and Abelian proton-operator neutrality construct a supported dimension-six
`qque` operator class whose residual ordinary Abelian character is trivial. -/
noncomputable def supportedInvariantOperator
    (S : OrdinaryAbelianBranchSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  ordinaryAbelianProjectedSource_supportedInvariantOperator
    S.toStandardProjectedSource

/-- Literal universal selection-rule conclusion: the branch source cannot
charge-forbid every supported physically admissible `Delta B = 1` local
operator. -/
theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : OrdinaryAbelianBranchSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Conditional E assembly at the local-operator level.  The positive witness
above refutes an ordinary Abelian charge rule that would forbid every
physically admissible standard proton-operator class. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : OrdinaryAbelianBranchSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Conditional E assembly with the dynamical channel-presence premise left
explicit: if either standard gauge-mediated channel is present, the ordinary
Abelian residual charge rule cannot forbid every present channel. -/
theorem not_forbidsPresentGaugeChannels
    (S : OrdinaryAbelianBranchSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

/-- Finite Abelian specialization of the local-operator assembly. -/
theorem finiteAbelian_not_forbidsEverySupportedProtonOperator
    [Finite H] (S : OrdinaryAbelianBranchSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator
    S.toStandardProjectedSource

/-- Finite-Abelian specialization of the universal local-operator result. -/
theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H] (S : OrdinaryAbelianBranchSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite Abelian specialization with an explicit present-channel premise. -/
theorem finiteAbelian_not_forbidsPresentGaugeChannels
    [Finite H] (S : OrdinaryAbelianBranchSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

end OrdinaryAbelianBranchSource

/-!
## Final assembly with semisimple embedding classification geometry constructed internally
-/

/-- Physical source interface in which the semisimple embedding classification decomposition and hypercharge
cocharacter are no longer supplied as certificates.  They are constructed
from `geometry` by the checked differentiable semisimple embedding classification bridge and the checked
physical-centralizer lattice theorem.

The two branchwise chiral-spectrum identifications remain explicit physical
inputs.  This structure therefore closes the semisimple embedding classification-to-E mathematical connection
without pretending to derive a low-energy spectrum or a nonzero decay channel
from group theory alone. -/
structure MatrixDifferentiableOrdinaryAbelianSource
    (H : Type u) [CommGroup H] where
  geometry : MatrixDifferentiableHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  hypercharge_oriented_neutrality :
    (geometry.hyperchargePair.2 = 0 ∧
        0 < geometry.hyperchargePair.1) ∨
      (singletExponent geometry.hyperchargePair = 0 ∧
        0 < geometry.hyperchargePair.2)
  standardSpectrum :
    geometry.hyperchargePair = standardPair →
      IsExactSMOnlyCoefficientSpectrum
        (ordinaryAbelianResolvedCharacter
          (geometry.iota : ProductGroup →*
            CompactEmbeddingClassification.SU6)
          geometry.weakDoubletData matter)
        generations physicalCharges singlets
  flippedSpectrum :
    geometry.hyperchargePair = flippedPair →
      ∀ t : NormalizedVirtualRestriction.DiagonalSU6Point,
        VirtualRestriction.FiniteVirtualSU6Representation.restrictedCharacter
            matter.toFiniteVirtual t =
          NormalizedVirtualRestriction.diagonalLaurentEval
            (Flipped.Normalized.zscale generations
                Flipped.Normalized.flippedSMCharacter +
              Flipped.Normalized.singletCharacter
                (totalSingletIndex singlets)) t

namespace MatrixDifferentiableOrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- Forget only the newly constructed geometry layer, yielding exactly the
previous checked branchwise assembly source. -/
noncomputable def toBranchSource
    (S : MatrixDifferentiableOrdinaryAbelianSource H) :
    OrdinaryAbelianBranchSource H where
  iota := S.geometry.iota
  weakDoubletData := S.geometry.weakDoubletData
  hyperchargePair := S.geometry.hyperchargePair
  hypercharge_injective := S.geometry.physicalCircleHom_injective
  hypercharge_oriented_neutrality :=
    S.hypercharge_oriented_neutrality
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  standardSpectrum := S.standardSpectrum
  flippedSpectrum := S.flippedSpectrum

/-- In the internally constructed coordinates, the actual hypercharge circle
must be the standard branch. -/
theorem hyperchargePair_eq_standard
    (S : MatrixDifferentiableOrdinaryAbelianSource H) :
    S.geometry.hyperchargePair = standardPair :=
  S.toBranchSource.hyperchargePair_eq_standard

/-- Concrete invariant local-operator witness transported through the
internally constructed semisimple embedding classification geometry. -/
noncomputable def supportedInvariantOperator
    (S : MatrixDifferentiableOrdinaryAbelianSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.toBranchSource.supportedInvariantOperator

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : MatrixDifferentiableOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- A differentiable actual embedding satisfying the explicit physical
spectrum inputs cannot have an ordinary Abelian charge rule that forbids every
supported proton-operator sector. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : MatrixDifferentiableOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Present-channel form of the differentiable semisimple embedding classification-to-D-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality
assembly. -/
theorem not_forbidsPresentGaugeChannels
    (S : MatrixDifferentiableOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  S.toBranchSource.not_forbidsPresentGaugeChannels hPresent

/-- Finite Abelian specialization of the local-operator theorem with semisimple embedding classification
geometry constructed internally. -/
theorem finiteAbelian_not_forbidsEverySupportedProtonOperator
    [Finite H] (S : MatrixDifferentiableOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.toBranchSource.finiteAbelian_not_forbidsEverySupportedProtonOperator

theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H] (S : MatrixDifferentiableOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite Abelian present-channel theorem with semisimple embedding classification geometry constructed
internally. -/
theorem finiteAbelian_not_forbidsPresentGaugeChannels
    [Finite H] (S : MatrixDifferentiableOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  S.toBranchSource.finiteAbelian_not_forbidsPresentGaugeChannels hPresent

end MatrixDifferentiableOrdinaryAbelianSource

/-!
## Alternative semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality assembly
-/

/-- A differentiable ordinary-Abelian source whose uncharged physical-torus
character is supplied directly.  hypercharge character rigidity then fixes the hypercharge cocharacter to
the standard pair, so this route needs neither an oriented-neutral-block
hypothesis nor a flipped-spectrum certificate.

The charge-resolved coefficient spectrum remains a separate standard charge-orbit bridge physical
input.  The flipped Weyl obstruction D remains an independent theorem and is
not used by this alternative assembly. -/
structure MatrixDifferentiableB3OrdinaryAbelianSource
    (H : Type u) [CommGroup H] where
  geometry : MatrixDifferentiableHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  physicalTorusSpectrum :
    PhysicalTorusCharacterBridge.IsExactSMCharacterOnPhysicalTorus
      (chi := matter.toFiniteVirtual)
      generations (totalSingletIndex singlets)
      geometry.hyperchargePair.1 geometry.hyperchargePair.2
  chargedSpectrum :
    geometry.hyperchargePair = standardPair →
      IsExactSMOnlyCoefficientSpectrum
        (ordinaryAbelianResolvedCharacter
          (geometry.iota : ProductGroup →*
            CompactEmbeddingClassification.SU6)
          geometry.weakDoubletData matter)
        generations physicalCharges singlets

namespace MatrixDifferentiableB3OrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- The checked hypercharge character rigidity finite-weight theorem selects the standard cocharacter
directly from the actual physical-torus character. -/
theorem hyperchargePair_eq_standard
    (S : MatrixDifferentiableB3OrdinaryAbelianSource H) :
    S.geometry.hyperchargePair = standardPair := by
  have hStandard :=
    PhysicalTorusCharacterBridge.eq_standard_of_virtualModel_characterOnPhysicalTorus
      S.matter.ambientLaurentModel S.generations
      (totalSingletIndex S.singlets)
      S.geometry.hyperchargePair.1 S.geometry.hyperchargePair.2
      S.generations_ne S.physicalTorusSpectrum
  apply Prod.ext
  · simpa [standardPair] using hStandard.1
  · simpa [standardPair] using hStandard.2

/-- Package the hypercharge character rigidity-selected standard branch into the exact strict ordinary
Abelian standard charge-orbit bridge source. -/
def toStandardProjectedSource
    (S : MatrixDifferentiableB3OrdinaryAbelianSource H) :
    PureSMOrdinaryAbelianProjectedSource H where
  iota := S.geometry.iota
  weakDoubletData := S.geometry.weakDoubletData
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  spectrum := S.chargedSpectrum S.hyperchargePair_eq_standard

/-- Concrete invariant local-operator witness along the independent
semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality route. -/
noncomputable def supportedInvariantOperator
    (S : MatrixDifferentiableB3OrdinaryAbelianSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  ordinaryAbelianProjectedSource_supportedInvariantOperator
    S.toStandardProjectedSource

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : MatrixDifferentiableB3OrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Local-operator semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality obstruction for an arbitrary
ordinary Abelian residual group. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : MatrixDifferentiableB3OrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Present-channel semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality obstruction. -/
theorem not_forbidsPresentGaugeChannels
    (S : MatrixDifferentiableB3OrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

/-- Finite Abelian specialization of the hypercharge character rigidity local-operator route. -/
theorem finiteAbelian_not_forbidsEverySupportedProtonOperator
    [Finite H] (S : MatrixDifferentiableB3OrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator
    S.toStandardProjectedSource

theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H] (S : MatrixDifferentiableB3OrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite Abelian present-channel specialization of the hypercharge character rigidity route. -/
theorem finiteAbelian_not_forbidsPresentGaugeChannels
    [Finite H] (S : MatrixDifferentiableB3OrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

end MatrixDifferentiableB3OrdinaryAbelianSource

/-!
## Single-spectrum semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality assembly
-/

/-- The strengthened physical source interface uses one finite
charge-resolved physical-torus spectrum at the actual cocharacter pair.
Forgetting charges supplies hypercharge character rigidity; after hypercharge character rigidity fixes `(-2,3)`, injectivity of the
standard key embedding supplies the standard charge-orbit bridge coefficient spectrum. -/
structure MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource
    (H : Type u) [CommGroup H] where
  geometry : MatrixDifferentiableHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  spectrum :
    PhysicalChargeResolvedBridge.IsExactSMOnlyPhysicalCoefficientSpectrum
      (PhysicalChargeResolvedBridge.ordinaryPhysicalResolvedCharacter
        geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter)
      generations physicalCharges singlets

namespace MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- The charge-forgetting projection of the single physical spectrum invokes
hypercharge character rigidity and fixes the actual hypercharge cocharacter. -/
theorem hyperchargePair_eq_standard
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    S.geometry.hyperchargePair = standardPair := by
  have hStandard :=
    PhysicalChargeResolvedBridge.ordinary_eq_standard_of_exactResolved
      S.matter S.generations S.physicalCharges S.singlets
      S.geometry.hyperchargePair.1 S.geometry.hyperchargePair.2
      S.generations_ne S.spectrum.resolvedCharacter_eq
  apply Prod.ext
  · simpa [standardPair] using hStandard.1
  · simpa [standardPair] using hStandard.2

/-- The same spectrum certificate, rather than a second independent field,
recovers the exact normalized standard charge-orbit bridge coefficients. -/
theorem coefficientSpectrum
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter)
      S.generations S.physicalCharges S.singlets :=
  PhysicalChargeResolvedBridge.ordinaryCoefficientSpectrum_of_exactResolved
    (S.geometry.iota : ProductGroup →*
      CompactEmbeddingClassification.SU6)
    S.geometry.weakDoubletData S.matter S.generations
    S.physicalCharges S.singlets
    S.geometry.hyperchargePair.1 S.geometry.hyperchargePair.2
    S.generations_ne S.spectrum.resolvedCharacter_eq

/-- Package the derived standard charge-orbit bridge spectrum into the checked standard projected
source. -/
def toStandardProjectedSource
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    PureSMOrdinaryAbelianProjectedSource H where
  iota := S.geometry.iota
  weakDoubletData := S.geometry.weakDoubletData
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  spectrum := S.coefficientSpectrum

/-- Concrete invariant local-operator witness obtained from one exact
charge-resolved physical spectrum. -/
noncomputable def supportedInvariantOperator
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  ordinaryAbelianProjectedSource_supportedInvariantOperator
    S.toStandardProjectedSource

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Local-operator obstruction from one exact physical spectrum for an
arbitrary ordinary Abelian residual group. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Present-channel obstruction from the single physical spectrum. -/
theorem not_forbidsPresentGaugeChannels
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

/-- Finite Abelian local-operator specialization. -/
theorem finiteAbelian_not_forbidsEverySupportedProtonOperator
    [Finite H]
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator
    S.toStandardProjectedSource

theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H]
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite Abelian present-channel specialization. -/
theorem finiteAbelian_not_forbidsPresentGaugeChannels
    [Finite H]
    (S : MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

end MatrixDifferentiablePhysicalSpectrumOrdinaryAbelianSource

/-!
## Chiral-index mass semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality assembly
-/

/-- A differentiable strict ordinary-Abelian source whose physical
low-energy input is exactly a character-level chiral-index equality.  It
requires an actual equivariant mass map, but no separately chosen
representation equivalences for its kernel and orthogonal cokernel. -/
structure MatrixDifferentiableChiralIndexOrdinaryAbelianSource
    (H : Type u) [CommGroup H] where
  geometry : MatrixDifferentiableHyperchargeEmbedding
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  massMap : Representation.IntertwiningMap
    (ordinaryPositiveRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
    (ordinaryNegativeRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  lightIndexMatchesTarget :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.CharacterEquivalent
      (EquivariantMassIndex.lightIndex massMap
        (ordinaryNegativeRepresentation
          geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).unitary)
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter
          generations physicalCharges singlets))

namespace MatrixDifferentiableChiralIndexOrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- Combine the semisimple embedding classification geometry with the character-level physical mass-index
source. -/
noncomputable def toPhysicalSource
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    PhysicalMassSpectrumBridge.OrdinaryChiralIndexSource H where
  iota := S.geometry.iota
  weakDoubletData := S.geometry.weakDoubletData
  matter := S.matter
  hyperchargeColor := S.geometry.hyperchargePair.1
  hyperchargeWeak := S.geometry.hyperchargePair.2
  massMap := S.massMap
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.physicalCharges
  singlets := S.singlets
  lightIndexMatchesTarget := S.lightIndexMatchesTarget

/-- The physical chiral index invokes hypercharge character rigidity and fixes the actual cocharacter. -/
theorem hyperchargePair_eq_standard
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    S.geometry.hyperchargePair = standardPair := by
  have hStandard := S.toPhysicalSource.hyperchargePair_eq_standard
  apply Prod.ext
  · simpa [toPhysicalSource, standardPair] using hStandard.1
  · simpa [toPhysicalSource, standardPair] using hStandard.2

/-- After hypercharge character rigidity, the same chiral-index equality supplies the normalized standard charge-orbit bridge
coefficient spectrum. -/
theorem coefficientSpectrum
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter)
      S.generations S.physicalCharges S.singlets :=
  S.toPhysicalSource.standardCoefficientSpectrum

/-- Package the chiral-index-derived standard charge-orbit bridge input. -/
noncomputable def toStandardProjectedSource
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    PureSMOrdinaryAbelianProjectedSource H :=
  S.toPhysicalSource.toProjectedSource

/-- The mass-index equality produces a concrete supported local operator
with trivial residual character.  No dynamical channel premise is used. -/
noncomputable def supportedInvariantOperator
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  ordinaryAbelianProjectedSource_supportedInvariantOperator
    S.toStandardProjectedSource

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- standard charge-orbit bridge followed by Abelian proton-operator neutrality at the local-operator level, with no dynamical channel
premise. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Present-channel form.  Existence of a nonzero channel remains an
independent physical premise. -/
theorem not_forbidsPresentGaugeChannels
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

/-- Finite-Abelian local-operator specialization of the chiral-index
route. -/
theorem finiteAbelian_not_forbidsEverySupportedProtonOperator
    [Finite H]
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator
    S.toStandardProjectedSource

theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H]
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite-Abelian present-channel specialization. -/
theorem finiteAbelian_not_forbidsPresentGaugeChannels
    [Finite H]
    (S : MatrixDifferentiableChiralIndexOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

end MatrixDifferentiableChiralIndexOrdinaryAbelianSource

/-!
## Invariant-mass-pairing semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality assembly
-/

/-- A physically phrased variant of the chiral-index source.  Instead of
assuming a bundled intertwiner, it assumes invariance of the Hermitian mass
pairing under the combined physical-torus and ordinary Abelian action.  The
intertwiner used by the mass index is then a theorem.

The remaining `lightIndexMatchesTarget` field is exactly the declared
low-energy SM-plus-singlets chiral-spectrum assumption. -/
structure MatrixDifferentiableInvariantMassPairingSource
    (H : Type u) [CommGroup H] where
  geometry : MatrixDifferentiableHyperchargeEmbedding
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  massPairing : EquivariantMassIndex.InvariantMassPairing
    (ordinaryPositiveRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
    (ordinaryNegativeRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  lightIndexMatchesTarget :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.CharacterEquivalent
      (EquivariantMassIndex.lightIndex
        (massPairing.toIntertwiningMap
          (ordinaryNegativeRepresentation
            geometry.hyperchargePair.1 geometry.hyperchargePair.2
            matter).unitary)
        (ordinaryNegativeRepresentation
          geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).unitary)
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter
          generations physicalCharges singlets))

namespace MatrixDifferentiableInvariantMassPairingSource

variable {H : Type u} [CommGroup H]

/-- The invariant Hermitian pairing supplies the equivariant mass map. -/
noncomputable def massMap
    (S : MatrixDifferentiableInvariantMassPairingSource H) :
    Representation.IntertwiningMap
      (ordinaryPositiveRepresentation
        S.geometry.hyperchargePair.1 S.geometry.hyperchargePair.2 S.matter).rho
      (ordinaryNegativeRepresentation
        S.geometry.hyperchargePair.1 S.geometry.hyperchargePair.2 S.matter).rho :=
  S.massPairing.toIntertwiningMap
    (ordinaryNegativeRepresentation
      S.geometry.hyperchargePair.1 S.geometry.hyperchargePair.2
      S.matter).unitary

/-- Forget only the Lagrangian-style presentation of mass invariance. -/
noncomputable def toChiralIndexSource
    (S : MatrixDifferentiableInvariantMassPairingSource H) :
    MatrixDifferentiableChiralIndexOrdinaryAbelianSource H where
  geometry := S.geometry
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  massMap := S.massMap
  lightIndexMatchesTarget := S.lightIndexMatchesTarget

theorem hyperchargePair_eq_standard
    (S : MatrixDifferentiableInvariantMassPairingSource H) :
    S.geometry.hyperchargePair = standardPair :=
  S.toChiralIndexSource.hyperchargePair_eq_standard

theorem coefficientSpectrum
    (S : MatrixDifferentiableInvariantMassPairingSource H) :
    IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter)
      S.generations S.physicalCharges S.singlets :=
  S.toChiralIndexSource.coefficientSpectrum

/-- Positive local-operator witness derived from invariant mass-pairing data. -/
noncomputable def supportedInvariantOperator
    (S : MatrixDifferentiableInvariantMassPairingSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.toChiralIndexSource.supportedInvariantOperator

/-- Scoped ordinary-Abelian selection-rule obstruction from an invariant mass
pairing and the exact low-energy chiral-index assumption. -/
theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : MatrixDifferentiableInvariantMassPairingSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Compatibility form using only the two canonical standard classes. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : MatrixDifferentiableInvariantMassPairingSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Finite-Abelian specialization of the literal universal conclusion. -/
theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H] (S : MatrixDifferentiableInvariantMassPairingSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Optional present-channel corollary. -/
theorem not_forbidsPresentGaugeChannels
    (S : MatrixDifferentiableInvariantMassPairingSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  S.toChiralIndexSource.not_forbidsPresentGaugeChannels hPresent

end MatrixDifferentiableInvariantMassPairingSource

/-!
## Continuity-only invariant-mass-pairing assembly
-/

/-- The physically phrased mass-pairing source with no differentiability
field.  Automatic regularity constructs the legacy differentiable geometry,
after which the existing `semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality` assembly applies unchanged. -/
structure ContinuousInvariantMassPairingSource
    (H : Type u) [CommGroup H] where
  geometry : ContinuousHyperchargeEmbedding
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  massPairing : EquivariantMassIndex.InvariantMassPairing
    (ordinaryPositiveRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
    (ordinaryNegativeRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  lightIndexMatchesTarget :
    PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.CharacterEquivalent
      (EquivariantMassIndex.lightIndex
        (massPairing.toIntertwiningMap
          (ordinaryNegativeRepresentation
            geometry.hyperchargePair.1 geometry.hyperchargePair.2
            matter).unitary)
        (ordinaryNegativeRepresentation
          geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).unitary)
      (PhysicalChargeResolvedEvaluation.ofCharacter
        (exactSMWithSingletsResolvedCharacter
          generations physicalCharges singlets))

namespace ContinuousInvariantMassPairingSource

variable {H : Type u} [CommGroup H]

/-- Forget only that automatic regularity supplied the differentiability
certificate. -/
noncomputable def toMatrixDifferentiableSource
    (S : ContinuousInvariantMassPairingSource H) :
    MatrixDifferentiableInvariantMassPairingSource H where
  geometry := S.geometry.toMatrixDifferentiable
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  massPairing := S.massPairing
  lightIndexMatchesTarget := S.lightIndexMatchesTarget

/-- hypercharge character rigidity fixes the hypercharge cocharacter from the exact light spectrum after
semisimple embedding classification has been obtained from continuity alone. -/
theorem hyperchargePair_eq_standard
    (S : ContinuousInvariantMassPairingSource H) :
    S.geometry.hyperchargePair = standardPair :=
  S.toMatrixDifferentiableSource.hyperchargePair_eq_standard

/-- The exact charge-resolved standard charge-orbit bridge spectrum recovered by the continuity-only
assembly. -/
theorem coefficientSpectrum
    (S : ContinuousInvariantMassPairingSource H) :
    IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter)
      S.generations S.physicalCharges S.singlets :=
  S.toMatrixDifferentiableSource.coefficientSpectrum

/-- Positive gauge- and Lorentz-invariant local-operator witness with trivial
ordinary Abelian residual character. -/
noncomputable def supportedInvariantOperator
    (S : ContinuousInvariantMassPairingSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.toMatrixDifferentiableSource.supportedInvariantOperator

/-- Continuity-only scoped ordinary-Abelian selection-rule obstruction. -/
theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : ContinuousInvariantMassPairingSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite-Abelian specialization of the continuity-only obstruction. -/
theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H] (S : ContinuousInvariantMassPairingSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

end ContinuousInvariantMassPairingSource

/-!
## Mass-index semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality assembly
-/

/-- A differentiable strict ordinary-Abelian source whose low-energy spectrum
is specified structurally by an equivariant mass map.  The ultraviolet signed
representation is constructed canonically from `matter`; the sole remaining
spectrum input identifies the unmatched light index with the
SM-plus-singlets target. -/
structure MatrixDifferentiableMassOrdinaryAbelianSource
    (H : Type u) [CommGroup H] where
  geometry : MatrixDifferentiableHyperchargeEmbedding
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  massMap : Representation.IntertwiningMap
    (ordinaryPositiveRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
    (ordinaryNegativeRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  lightSpectrumEquiv :
    PhysicalLightSpectrumBridge.LightSpectrumEquiv massMap
      (ordinaryNegativeRepresentation
        geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).unitary
      (exactSMWithSingletsResolvedCharacter
        generations physicalCharges singlets)

namespace MatrixDifferentiableMassOrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- Package the actual semisimple embedding classification geometry and structural mass data into the checked
physical mass-index bridge. -/
noncomputable def toMassSource
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    PhysicalMassSpectrumBridge.OrdinarySource H where
  iota := S.geometry.iota
  weakDoubletData := S.geometry.weakDoubletData
  matter := S.matter
  hyperchargeColor := S.geometry.hyperchargePair.1
  hyperchargeWeak := S.geometry.hyperchargePair.2
  massMap := S.massMap
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.physicalCharges
  singlets := S.singlets
  lightSpectrumEquiv := S.lightSpectrumEquiv

/-- The mass-derived charge-resolved spectrum invokes hypercharge character rigidity and fixes the actual
cocharacter extracted from the physical hypercharge circle. -/
theorem hyperchargePair_eq_standard
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    S.geometry.hyperchargePair = standardPair := by
  have hStandard := S.toMassSource.hyperchargePair_eq_standard
  apply Prod.ext
  · simpa [toMassSource, standardPair] using hStandard.1
  · simpa [toMassSource, standardPair] using hStandard.2

/-- The same mass index supplies the exact normalized standard charge-orbit bridge coefficient
spectrum after hypercharge character rigidity fixes the pair. -/
theorem coefficientSpectrum
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter)
      S.generations S.physicalCharges S.singlets :=
  S.toMassSource.standardCoefficientSpectrum

/-- Package the mass-derived standard charge-orbit bridge input in the standard projected-source
interface. -/
noncomputable def toStandardProjectedSource
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    PureSMOrdinaryAbelianProjectedSource H :=
  S.toMassSource.toProjectedSource

/-- Concrete invariant local-operator witness derived from the structural
mass source. -/
noncomputable def supportedInvariantOperator
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  ordinaryAbelianProjectedSource_supportedInvariantOperator
    S.toStandardProjectedSource

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Local-operator ordinary-Abelian obstruction derived from the structural
mass source. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Present-channel form; channel existence remains an explicit physical
premise independent of the character calculation. -/
theorem not_forbidsPresentGaugeChannels
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

/-- Finite-Abelian local-operator specialization of the structural mass
route. -/
theorem finiteAbelian_not_forbidsEverySupportedProtonOperator
    [Finite H]
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator
    S.toStandardProjectedSource

theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H]
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite-Abelian present-channel specialization of the structural mass
route. -/
theorem finiteAbelian_not_forbidsPresentGaugeChannels
    [Finite H]
    (S : MatrixDifferentiableMassOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  finiteAbelian_ordinaryAbelianProjectedSource_not_forbids_of_present
    S.toStandardProjectedSource hPresent

end MatrixDifferentiableMassOrdinaryAbelianSource

/-!
## Unitarily block-decomposed semisimple embedding classification-to-hypercharge character rigidity-to-standard charge-orbit bridge-to-Abelian proton-operator neutrality assembly
-/

/-- A differentiable strict ordinary-Abelian source whose physical input is
an explicit unitary decomposition into target light modes and a common heavy
sector.  The equivariant mass map and its kernel/cokernel identifications are
constructed by `UnitaryBlockMass`. -/
structure MatrixDifferentiableBlockMassOrdinaryAbelianSource
    (H : Type u) [CommGroup H] where
  geometry : MatrixDifferentiableHyperchargeEmbedding
  matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightHeavyDecomposition : PhysicalLightSpectrumBridge.BlockDecomposition
    (ordinaryPositiveRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter)
    (ordinaryNegativeRepresentation
      geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter)
    (exactSMWithSingletsResolvedCharacter
      generations physicalCharges singlets)

namespace MatrixDifferentiableBlockMassOrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- Package the geometry and light-heavy decomposition in the physical block
source interface. -/
noncomputable def toBlockSource
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    PhysicalMassSpectrumBridge.BlockSource H where
  iota := S.geometry.iota
  weakDoubletData := S.geometry.weakDoubletData
  matter := S.matter
  hyperchargeColor := S.geometry.hyperchargePair.1
  hyperchargeWeak := S.geometry.hyperchargePair.2
  generations := S.generations
  generations_ne := S.generations_ne
  charges := S.physicalCharges
  singlets := S.singlets
  lightHeavyDecomposition := S.lightHeavyDecomposition

/-- Forget the explicit normal form after constructing its mass map. -/
noncomputable def toMassSource
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    MatrixDifferentiableMassOrdinaryAbelianSource H where
  geometry := S.geometry
  matter := S.matter
  generations := S.generations
  generations_ne := S.generations_ne
  physicalCharges := S.physicalCharges
  singlets := S.singlets
  massMap := S.lightHeavyDecomposition.massMap
  lightSpectrumEquiv := S.lightHeavyDecomposition.lightSpectrumEquiv

/-- hypercharge character rigidity fixes the actual hypercharge cocharacter for a block-decomposed
source. -/
theorem hyperchargePair_eq_standard
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    S.geometry.hyperchargePair = standardPair :=
  S.toMassSource.hyperchargePair_eq_standard

/-- The same decomposition supplies the exact standard charge-orbit bridge coefficient spectrum. -/
theorem coefficientSpectrum
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter)
      S.generations S.physicalCharges S.singlets :=
  S.toMassSource.coefficientSpectrum

/-- Package the block-derived standard charge-orbit bridge input. -/
noncomputable def toStandardProjectedSource
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    PureSMOrdinaryAbelianProjectedSource H :=
  S.toMassSource.toStandardProjectedSource

/-- Concrete invariant local-operator witness for the explicit light-heavy
decomposition. -/
noncomputable def supportedInvariantOperator
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.toMassSource.supportedInvariantOperator

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- standard charge-orbit bridge followed by Abelian proton-operator neutrality for the explicit light-heavy decomposition. -/
theorem not_forbidsEverySupportedProtonOperator
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.supportedInvariantOperator.not_forbidsEverySupportedStandardOperator

/-- Present-channel version; channel existence remains an independent
physical premise. -/
theorem not_forbidsPresentGaugeChannels
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  S.toMassSource.not_forbidsPresentGaugeChannels hPresent

/-- Finite-Abelian local-operator specialization. -/
theorem finiteAbelian_not_forbidsEverySupportedProtonOperator
    [Finite H]
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.toMassSource.finiteAbelian_not_forbidsEverySupportedProtonOperator

theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H]
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (S.geometry.iota : ProductGroup →*
          CompactEmbeddingClassification.SU6)
        S.geometry.weakDoubletData S.matter) :=
  S.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Finite-Abelian present-channel specialization. -/
theorem finiteAbelian_not_forbidsPresentGaugeChannels
    [Finite H]
    (S : MatrixDifferentiableBlockMassOrdinaryAbelianSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  S.toMassSource.finiteAbelian_not_forbidsPresentGaugeChannels hPresent

end MatrixDifferentiableBlockMassOrdinaryAbelianSource

end FinalNoGoAssembly

end
end GUT
