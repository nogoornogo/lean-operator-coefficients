import Physics.FieldTheory.Yukawa.Mass.DiracYukawaMass
import GUT.SU6.SelectionRules.FinalNoGoAssembly

open Physics

open Math

/-!
# Finite-dimensional Dirac mass models for the SU(6) no-go theorem

This module is the scoped physical-source layer for the first completed mass
model.  It combines continuous semisimple embedding classification geometry and strict ordinary Abelian matter
with a finite-dimensional Dirac-type Yukawa sector over the unbroken physical
torus and residual group.

The Standard Model condition is deliberately an equality of charge-resolved
massless chiral indices.  It is an applicability condition and allows
additional vectorlike zero-mode pairs.  The Yukawa and vacuum data, rather
than an exposed intertwiner or invariant Hermitian pairing, construct the mass
map consumed by the checked `semisimple embedding classification -> hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality` assembly.

This module does not cover a general two-component Weyl or Majorana mass
bilinear and does not claim that every physical residual Abelian symmetry is
strictly commuting with the ultraviolet `SU(6)` action.
-/

namespace GUT
namespace DiracPhysicalModel

open DiracYukawaMass
open CompactEmbeddingClassification
open EquivariantMassIndex
open FinalNoGoAssembly
open FiniteAbelianChargeSectors
open PhysicalChargeResolvedEvaluation
open PhysicalMassSpectrumBridge
open PhysicalRestrictionBridge
open StandardAbelianProtection
open StandardBlockGaugeCancellation
open StandardBlockChargeProjection
open StandardBranchProtonObstruction
open StandardModelLocalOperator
open StandardPhysicalSpectrumBridge
open UnitaryVirtualRealization

noncomputable section

universe u

abbrev CombinedGroup (H : Type u) :=
  PhysicalChargeResolvedEvaluation.CombinedGroup H

abbrev ResidualCharge (H : Type u) [Group H] :=
  FiniteAbelianChargeSectors.ChargeLabel H

/-- The exact charge-resolved massless chiral-index condition used by E.
This is weaker than identifying the complete kernel and cokernel separately. -/
def HasExactSMChiralIndex
    {H : Type u} [CommGroup H]
    {V : Type} {W : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W]
    {rhoV : Representation ℂ (CombinedGroup H) V}
    {rhoW : Representation ℂ (CombinedGroup H) W}
    (massMap : Representation.IntertwiningMap rhoV rhoW)
    (hW : IsUnitaryRepresentation rhoW)
    (generations : ℤ)
    (physicalCharges : Charges (ResidualCharge H))
    (singlets : ResidualCharge H →₀ ℤ) : Prop :=
  FiniteVirtualGroupRepresentation.CharacterEquivalent
    (lightIndex massMap hW)
    (PhysicalChargeResolvedEvaluation.ofCharacter
      (PhysicalChargeResolvedBridge.exactSMWithSingletsResolvedCharacter
        generations physicalCharges singlets))

/-- The canonical positive signed sector of a strict ordinary Abelian source
at the cocharacter extracted from the continuous geometry. -/
abbrev positiveRepresentation
    {H : Type u} [CommGroup H]
    (geometry : ContinuousHyperchargeEmbedding)
    (matter : OrdinaryAbelianSource H) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) :=
  ordinaryPositiveRepresentation
    geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter

/-- The canonical negative signed sector of a strict ordinary Abelian source
at the cocharacter extracted from the continuous geometry. -/
abbrev negativeRepresentation
    {H : Type u} [CommGroup H]
    (geometry : ContinuousHyperchargeEmbedding)
    (matter : OrdinaryAbelianSource H) :
    ActualUnitaryGroupRepresentation (CombinedGroup H) :=
  ordinaryNegativeRepresentation
    geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter

/-- A finite-dimensional post-SU(6)-breaking, pre-electroweak Dirac-type
mass model.  The candidate exact ordinary Abelian action is carried by
`matter`; by construction it commutes with the full ultraviolet `SU(6)`
action.  The exact Standard Model chiral index remains an explicit physical
applicability condition. -/
structure ContinuousDiracYukawaModel
    (H : Type u) [CommGroup H] where
  geometry : ContinuousHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  scalar : ActualUnitaryGroupRepresentation (CombinedGroup H)
  generations : ℤ
  generations_ne : generations ≠ 0
  physicalCharges : Charges (ResidualCharge H)
  singlets : ResidualCharge H →₀ ℤ
  massSector : Sector scalar.rho
    (positiveRepresentation geometry matter).rho
    (negativeRepresentation geometry matter).rho
  hasExactSMChiralIndex : HasExactSMChiralIndex massSector.massMap
    (negativeRepresentation geometry matter).unitary
    generations physicalCharges singlets

namespace ContinuousDiracYukawaModel

variable {H : Type u} [CommGroup H]

/-- The induced post-vacuum Dirac mass intertwiner. -/
def massMap (M : ContinuousDiracYukawaModel H) :
    Representation.IntertwiningMap
      (positiveRepresentation M.geometry M.matter).rho
      (negativeRepresentation M.geometry M.matter).rho :=
  M.massSector.massMap

/-- The induced invariant Hermitian mass pairing used by the existing E
source. -/
def massPairing (M : ContinuousDiracYukawaModel H) :
    InvariantMassPairing
      (positiveRepresentation M.geometry M.matter).rho
      (negativeRepresentation M.geometry M.matter).rho :=
  M.massSector.toInvariantMassPairing
    (negativeRepresentation M.geometry M.matter).unitary

@[simp]
theorem massPairing_toIntertwiningMap
    (M : ContinuousDiracYukawaModel H) :
    M.massPairing.toIntertwiningMap
        (negativeRepresentation M.geometry M.matter).unitary =
      M.massMap :=
  M.massSector.toInvariantMassPairing_toIntertwiningMap
    (negativeRepresentation M.geometry M.matter).unitary

/-- Convert primitive Dirac Yukawa data to the already checked
continuity-only invariant-mass-pairing assembly. -/
def toInvariantMassPairingSource
    (M : ContinuousDiracYukawaModel H) :
    ContinuousInvariantMassPairingSource H where
  geometry := M.geometry
  matter := M.matter
  generations := M.generations
  generations_ne := M.generations_ne
  physicalCharges := M.physicalCharges
  singlets := M.singlets
  massPairing := M.massPairing
  lightIndexMatchesTarget := by
    simpa only [massPairing_toIntertwiningMap, massMap,
      HasExactSMChiralIndex] using M.hasExactSMChiralIndex

/-- hypercharge character rigidity fixes the actual hypercharge cocharacter for every model in the
Dirac-type class. -/
theorem hyperchargePair_eq_standard
    (M : ContinuousDiracYukawaModel H) :
    M.geometry.hyperchargePair = HyperchargeBranchArithmetic.standardPair :=
  M.toInvariantMassPairingSource.hyperchargePair_eq_standard

/-- The exact standard charge-orbit bridge coefficient profile derived from the chiral-index condition. -/
theorem coefficientSpectrum
    (M : ContinuousDiracYukawaModel H) :
    IsExactSMOnlyCoefficientSpectrum
      (ordinaryAbelianResolvedCharacter
        (M.geometry.iota : CompactEmbeddingClassification.ProductGroup →*
          CompactEmbeddingClassification.SU6)
        M.geometry.weakDoubletData M.matter)
      M.generations M.physicalCharges M.singlets :=
  M.toInvariantMassPairingSource.coefficientSpectrum

/-- A supported gauge- and Lorentz-invariant local operator class whose
ordinary Abelian residual character is trivial. -/
def supportedInvariantOperator
    (M : ContinuousDiracYukawaModel H) :
    SupportedInvariantOperator
      (ordinaryAbelianResolvedCharacter
        (M.geometry.iota : CompactEmbeddingClassification.ProductGroup →*
          CompactEmbeddingClassification.SU6)
        M.geometry.weakDoubletData M.matter) :=
  M.toInvariantMassPairingSource.supportedInvariantOperator

/-- The scoped Dirac-model theorem E: the strict ordinary Abelian charge rule
cannot prohibit every represented physical `Delta B = 1` local operator
class. -/
theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (M : ContinuousDiracYukawaModel H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (M.geometry.iota : CompactEmbeddingClassification.ProductGroup →*
          CompactEmbeddingClassification.SU6)
        M.geometry.weakDoubletData M.matter) :=
  M.toInvariantMassPairingSource.not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Compatibility form for the two canonical standard operator classes. -/
theorem not_forbidsEverySupportedProtonOperator
    (M : ContinuousDiracYukawaModel H) :
    ¬ ForbidsEverySupportedProtonOperator
      (ordinaryAbelianResolvedCharacter
        (M.geometry.iota : CompactEmbeddingClassification.ProductGroup →*
          CompactEmbeddingClassification.SU6)
        M.geometry.weakDoubletData M.matter) :=
  M.toInvariantMassPairingSource.toMatrixDifferentiableSource
    |>.not_forbidsEverySupportedProtonOperator

/-- Finite-Abelian specialization of the scoped Dirac-model theorem. -/
theorem finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator
    [Finite H] (M : ContinuousDiracYukawaModel H) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (ordinaryAbelianResolvedCharacter
        (M.geometry.iota : CompactEmbeddingClassification.ProductGroup →*
          CompactEmbeddingClassification.SU6)
        M.geometry.weakDoubletData M.matter) :=
  M.toInvariantMassPairingSource
    |>.finiteAbelian_not_forbidsEverySupportedPhysicalDeltaBOneOperator

/-- Any previously checked invariant-mass-pairing source embeds into the
Dirac-Yukawa interface by treating its mass map as an invariant bare mass and
taking a zero scalar sector.  This proves that the new primitive-data layer
introduces no extra algebraic consistency condition. -/
def ofInvariantMassPairingSource
    (M : ContinuousInvariantMassPairingSource H) :
    ContinuousDiracYukawaModel H where
  geometry := M.geometry
  matter := M.matter
  scalar := ActualUnitaryGroupRepresentation.zero
  generations := M.generations
  generations_ne := M.generations_ne
  physicalCharges := M.physicalCharges
  singlets := M.singlets
  massSector := Sector.ofBareMass
    (rhoS := (ActualUnitaryGroupRepresentation.zero :
      ActualUnitaryGroupRepresentation (CombinedGroup H)).rho)
    (InvariantBareMass.ofIntertwiningMap
      (M.massPairing.toIntertwiningMap
        (negativeRepresentation M.geometry M.matter).unitary))
  hasExactSMChiralIndex := by
    simpa only [HasExactSMChiralIndex, Sector.ofBareMass_massMap,
      InvariantBareMass.ofIntertwiningMap_toIntertwiningMap] using
      M.lightIndexMatchesTarget

/-- The compatibility lift preserves the mass intertwiner supplied by the
older invariant-pairing interface.  In particular, the Dirac primitive-data
layer adds no hidden algebraic restriction to that interface. -/
@[simp]
theorem ofInvariantMassPairingSource_massMap
    (M : ContinuousInvariantMassPairingSource H) :
    (ofInvariantMassPairingSource M).massMap =
      M.massPairing.toIntertwiningMap
        (negativeRepresentation M.geometry M.matter).unitary := by
  change
    (Sector.ofBareMass
      (rhoS := (ActualUnitaryGroupRepresentation.zero :
        ActualUnitaryGroupRepresentation (CombinedGroup H)).rho)
      (InvariantBareMass.ofIntertwiningMap
        (M.massPairing.toIntertwiningMap
          (negativeRepresentation M.geometry M.matter).unitary))).massMap = _
  rw [Sector.ofBareMass_massMap,
    InvariantBareMass.ofIntertwiningMap_toIntertwiningMap]

end ContinuousDiracYukawaModel

end
end DiracPhysicalModel
end GUT
