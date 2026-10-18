import GUT.SU6.Hypercharge.ActualBlockConjugacy
import Physics.StandardModel.Operators.StandardModelLocalOperator

open Math

/-!
# Interpreting the standard-branch charge obstruction

The standard charge-orbit bridge -> Abelian proton-operator neutrality calculation proves that both canonical proton-operator
characters are trivial.  Its primary interpretation here is purely a
selection-rule statement: a supported, gauge- and Lorentz-invariant
dimension-six local operator class has trivial residual character, whether or
not its Wilson coefficient is nonzero.

The older `firstPresent` and `secondPresent` interface is retained as an
optional stronger corollary.  Those propositions must be supplied by a
separate dynamical calculation.  No anomaly equation is used in either form.
-/

namespace GUT
namespace StandardAbelianProtection

open FiniteAbelianChargeSectors
open StandardBranchProtonObstruction
open StandardBlockChargeProjection
open StandardModelLocalOperator

noncomputable section

universe u

/-- Charge-theoretic criterion for an ordinary Abelian symmetry to forbid
every gauge-mediated channel that is physically present. -/
def ForbidsPresentGaugeChannels
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H))
    (firstPresent secondPresent : Prop) : Prop :=
  (firstPresent → protonFirstCharacter k ≠ 1) ∧
    (secondPresent → protonSecondCharacter k ≠ 1)

/-- Symmetry protection at the local-operator level: every charge assignment
supported by all five chiral Standard Model profiles must forbid both
gauge- and Lorentz-invariant dimension-six `qque` and `duql` operator classes.
Unlike `ForbidsPresentGaugeChannels`, this makes no assertion about a Wilson
coefficient or amplitude. -/
def ForbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H]
    (p : StandardAbelianCharge.ResolvedCharacter (ChargeLabel H)) : Prop :=
  ForbidsEverySupportedStandardOperator p

theorem forbidsEverySupportedProtonOperator_iff
    {H : Type u} [CommGroup H]
    (p : StandardAbelianCharge.ResolvedCharacter (ChargeLabel H)) :
    ForbidsEverySupportedProtonOperator p ↔
      ∀ k : Charges (ChargeLabel H),
        StandardAbelianCharge.ChargesSupported p k →
          protonFirstCharacter k ≠ 1 ∧ protonSecondCharacter k ≠ 1 :=
  forbidsEverySupportedStandardOperator_iff p

/-- If both proton-operator characters are trivial and at least one channel
is present, ordinary Abelian charge conservation cannot forbid every present
channel. -/
theorem not_forbidsPresentGaugeChannels_of_characters_eq_one
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H))
    {firstPresent secondPresent : Prop}
    (hNeutral : protonFirstCharacter k = 1 ∧
      protonSecondCharacter k = 1)
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels k firstPresent secondPresent := by
  intro hProtects
  rcases hPresent with hFirst | hSecond
  · exact (hProtects.1 hFirst) hNeutral.1
  · exact (hProtects.2 hSecond) hNeutral.2

/-- In particular, triviality of both characters excludes a charge selection
rule that purports to forbid both operator classes. -/
theorem not_forbidsBothGaugeChannels_of_characters_eq_one
    {H : Type u} [CommGroup H]
    (k : Charges (ChargeLabel H))
    (hNeutral : protonFirstCharacter k = 1 ∧
      protonSecondCharacter k = 1) :
    ¬ ForbidsPresentGaugeChannels k True True :=
  not_forbidsPresentGaugeChannels_of_characters_eq_one
    k hNeutral (Or.inl True.intro)

/-- Conditional present-channel interpretation theorem.  The source contains the
actual semisimple embedding classification block embedding, common centralizing gauge lift, charge-sector
matter, and exact coefficient-level SM spectrum.  Once a physical calculation
supplies at least one present gauge-mediated channel, its residual ordinary
Abelian symmetry cannot forbid all present channels. -/
theorem projectedSource_not_forbids_of_present
    {H : Type u} [CommGroup H]
    (S : PureSMActualBlockProjectedSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  not_forbidsPresentGaugeChannels_of_characters_eq_one
    S.physicalCharges S.protonCharacters_eq_one hPresent

/-- Specialization when both standard gauge-mediated operator classes are
present. -/
theorem projectedSource_not_forbids_both
    {H : Type u} [CommGroup H]
    (S : PureSMActualBlockProjectedSource H) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges True True :=
  not_forbidsBothGaugeChannels_of_characters_eq_one
    S.physicalCharges S.protonCharacters_eq_one

/-- Explicit finite-Abelian version.  No lifting of finite characters to a
continuous circle and no anomaly condition is used. -/
theorem finiteAbelian_projectedSource_not_forbids_of_present
    {H : Type u} [CommGroup H] [Finite H]
    (S : PureSMActualBlockProjectedSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  projectedSource_not_forbids_of_present S hPresent

/-- Family-dependent standard charge-orbit bridge-to-Abelian proton-operator neutrality selection-rule theorem.  A supported sector
with two trivial proton characters witnesses that the ordinary Abelian charge
rule cannot exclude every supported proton operator.  No channel-amplitude or
anomaly premise enters this statement. -/
noncomputable def projectedSource_supportedInvariantOperator
    {H : Type u} [CommGroup H]
    (S : PureSMActualBlockProjectedSource H) :
    SupportedInvariantOperator
      (actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
        S.gauge_centralizes S.matter) := by
  let hExists := S.exists_supported_neutral_proton_sectors
  let k := Classical.choose hExists
  have hk := Classical.choose_spec hExists
  exact supportedQque k hk.1
    (protonFirstCharacter_eq_one_of_eq_zero k hk.2.1)

/-- Primary selection-rule conclusion for the actual projected source: not
every supported physically admissible `Delta B = 1` local operator can carry
a nontrivial residual character. -/
theorem projectedSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H]
    (S : PureSMActualBlockProjectedSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
        S.gauge_centralizes S.matter) :=
  (projectedSource_supportedInvariantOperator S).not_forbidsEverySupportedPhysicalDeltaBOneOperator

theorem projectedSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H]
    (S : PureSMActualBlockProjectedSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
        S.gauge_centralizes S.matter) :=
  (projectedSource_supportedInvariantOperator S).not_forbidsEverySupportedStandardOperator

/-- The same charge-selection obstruction for a finite Abelian residual
group.  It is a specialization, not a reduction to a continuous `U(1)`
anomaly argument. -/
theorem finiteAbelian_projectedSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H] [Finite H]
    (S : PureSMActualBlockProjectedSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
        S.gauge_centralizes S.matter) :=
  projectedSource_not_forbidsEverySupportedProtonOperator S

/-- Finite-Abelian specialization of the literal universal local-operator
selection-rule conclusion. -/
theorem finiteAbelian_projectedSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H] [Finite H]
    (S : PureSMActualBlockProjectedSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (actualBlockResolvedCharacter S.iota S.weakDoubletData S.gauge
        S.gauge_centralizes S.matter) :=
  projectedSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator S

/-- standard charge-orbit bridge source theorem with only profile occupancy as its low-energy spectrum
input.  It applies to family-dependent residual charges and says that the
ordinary Abelian charge rule alone cannot exclude every supported proton
operator. -/
noncomputable def actualBlockSource_supportedInvariantOperator
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota)
    (matter : StandardBlockGaugeCancellation.CommonGaugeSource H gauge)
    (hTen : StandardAbelianCharge.quarkProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0) :
    SupportedInvariantOperator
      (actualBlockResolvedCharacter iota W gauge hCentral matter) := by
  let hExists :=
    actualBlockResolvedCharacter_exists_supported_neutral_proton_sectors
      iota W gauge hCentral matter hTen hBarFive
  let k := Classical.choose hExists
  have hk := Classical.choose_spec hExists
  exact supportedQque k hk.1
    (protonFirstCharacter_eq_one_of_eq_zero k hk.2.1)

theorem actualBlockSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota)
    (matter : StandardBlockGaugeCancellation.CommonGaugeSource H gauge)
    (hTen : StandardAbelianCharge.quarkProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (actualBlockResolvedCharacter iota W gauge hCentral matter) :=
  (actualBlockSource_supportedInvariantOperator
    iota W gauge hCentral matter hTen hBarFive).not_forbidsEverySupportedPhysicalDeltaBOneOperator

theorem actualBlockSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota)
    (matter : StandardBlockGaugeCancellation.CommonGaugeSource H gauge)
    (hTen : StandardAbelianCharge.quarkProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0) :
    ¬ ForbidsEverySupportedProtonOperator
      (actualBlockResolvedCharacter iota W gauge hCentral matter) :=
  (actualBlockSource_supportedInvariantOperator
    iota W gauge hCentral matter hTen hBarFive).not_forbidsEverySupportedStandardOperator

/-- Finite Abelian specialization of the occupancy-source local-operator
theorem. -/
theorem finiteAbelian_actualBlockSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H] [Finite H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota)
    (matter : StandardBlockGaugeCancellation.CommonGaugeSource H gauge)
    (hTen : StandardAbelianCharge.quarkProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0) :
    ¬ ForbidsEverySupportedProtonOperator
      (actualBlockResolvedCharacter iota W gauge hCentral matter) :=
  actualBlockSource_not_forbidsEverySupportedProtonOperator
    iota W gauge hCentral matter hTen hBarFive

theorem finiteAbelian_actualBlockSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H] [Finite H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈
      ActualCompactCentralizer.PhysicalCentralizer iota)
    (matter : StandardBlockGaugeCancellation.CommonGaugeSource H gauge)
    (hTen : StandardAbelianCharge.quarkProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (actualBlockResolvedCharacter iota W gauge hCentral matter) ≠ 0) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (actualBlockResolvedCharacter iota W gauge hCentral matter) :=
  actualBlockSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    iota W gauge hCentral matter hTen hBarFive

/-!
## Strict ordinary Abelian source conclusions

These statements remove the chosen common gauge lift from standard charge-orbit bridge.  Their source
data consist only of actual finite-dimensional continuous-unitary `SU(6)`
representations and unitary Abelian actions commuting with `SU(6)`.
-/

/-- Occupancy-level standard-branch obstruction for a strict ordinary
Abelian internal symmetry. -/
noncomputable def ordinaryAbelianSource_supportedInvariantOperator
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (hTen : StandardAbelianCharge.quarkProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter iota W matter) :=
  actualBlockSource_supportedInvariantOperator
    iota W (1 : H →* CompactEmbeddingClassification.SU6)
    (identityGauge_centralizes iota) matter.toCommonGaugeSource hTen hBarFive

theorem ordinaryAbelianSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (hTen : StandardAbelianCharge.quarkProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter iota W matter) :=
  (ordinaryAbelianSource_supportedInvariantOperator
    iota W matter hTen hBarFive).not_forbidsEverySupportedPhysicalDeltaBOneOperator

theorem ordinaryAbelianSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (hTen : StandardAbelianCharge.quarkProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter iota W matter) :=
  actualBlockSource_not_forbidsEverySupportedProtonOperator
    iota W (1 : H →* CompactEmbeddingClassification.SU6)
    (identityGauge_centralizes iota) matter.toCommonGaugeSource hTen hBarFive

/-- Finite Abelian specialization of the strict ordinary source theorem. -/
theorem finiteAbelian_ordinaryAbelianSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H] [Finite H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (hTen : StandardAbelianCharge.quarkProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter iota W matter) :=
  ordinaryAbelianSource_not_forbidsEverySupportedProtonOperator
    iota W matter hTen hBarFive

theorem finiteAbelian_ordinaryAbelianSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H] [Finite H]
    (iota : CompactEmbeddingClassification.ProductGroup →*
      CompactEmbeddingClassification.SU6)
    (W : ActualBlockCentralizer.WeakDoubletData
      (CompactEmbeddingClassification.euclideanDefiningRestriction iota))
    (matter : StandardBlockGaugeCancellation.OrdinaryAbelianSource H)
    (hTen : StandardAbelianCharge.quarkProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0)
    (hBarFive : StandardAbelianCharge.downProfile
      (ordinaryAbelianResolvedCharacter iota W matter) ≠ 0) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter iota W matter) :=
  ordinaryAbelianSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    iota W matter hTen hBarFive

/-- Exact-spectrum standard charge-orbit bridge-to-Abelian proton-operator neutrality selection-rule obstruction for an ordinary
Abelian internal symmetry.  This is logically independent of the continuous
`U(1)` anomaly cross-check. -/
noncomputable def ordinaryAbelianProjectedSource_supportedInvariantOperator
    {H : Type u} [CommGroup H]
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) := by
  let hExists := S.exists_supported_neutral_proton_sectors
  let k := Classical.choose hExists
  have hk := Classical.choose_spec hExists
  exact supportedQque k hk.1
    (protonFirstCharacter_eq_one_of_eq_zero k hk.2.1)

/-- Exact-spectrum form of the literal universal local-operator obstruction. -/
theorem ordinaryAbelianProjectedSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H]
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  (ordinaryAbelianProjectedSource_supportedInvariantOperator S).not_forbidsEverySupportedPhysicalDeltaBOneOperator

theorem ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H]
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  (ordinaryAbelianProjectedSource_supportedInvariantOperator S).not_forbidsEverySupportedStandardOperator

/-- Finite Abelian exact-spectrum specialization.  No continuous lift of a
finite character is used. -/
theorem finiteAbelian_ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator
    {H : Type u} [CommGroup H] [Finite H]
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  ordinaryAbelianProjectedSource_not_forbidsEverySupportedProtonOperator S

/-- Finite-Abelian exact-spectrum form of the universal local-operator
selection-rule obstruction. -/
theorem finiteAbelian_ordinaryAbelianProjectedSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    {H : Type u} [CommGroup H] [Finite H]
    (S : PureSMOrdinaryAbelianProjectedSource H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        S.iota S.weakDoubletData S.matter) :=
  ordinaryAbelianProjectedSource_not_forbidsEverySupportedPhysicalDeltaBOneOperator S

/-- Once either standard gauge-mediated channel is physically present, the
exact ordinary Abelian source cannot forbid every present channel. -/
theorem ordinaryAbelianProjectedSource_not_forbids_of_present
    {H : Type u} [CommGroup H]
    (S : PureSMOrdinaryAbelianProjectedSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  not_forbidsPresentGaugeChannels_of_characters_eq_one
    S.physicalCharges S.protonCharacters_eq_one hPresent

/-- Finite Abelian version of the present-channel interpretation. -/
theorem finiteAbelian_ordinaryAbelianProjectedSource_not_forbids_of_present
    {H : Type u} [CommGroup H] [Finite H]
    (S : PureSMOrdinaryAbelianProjectedSource H)
    {firstPresent secondPresent : Prop}
    (hPresent : firstPresent ∨ secondPresent) :
    ¬ ForbidsPresentGaugeChannels S.physicalCharges
      firstPresent secondPresent :=
  ordinaryAbelianProjectedSource_not_forbids_of_present S hPresent

end
end StandardAbelianProtection
end GUT
