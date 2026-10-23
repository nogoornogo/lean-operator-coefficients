import GUT.SU6.Hypercharge.ActualCompactCentralizer
import GUT.SU6.SelectionRules.StandardBranch.FiniteAbelianChargeSectors
import GUT.SU6.SelectionRules.StandardBranch.FiniteResidualActionFactorization
import GUT.SU6.SelectionRules.Models.StandardPhysicalSpectrumBridge
import Mathlib.Tactic

open Physics

open Math

/-!
# Cancellation of standard-branch block gauge phases

A representative of an ordinary Abelian residual symmetry may contain an
`SU(6)` gauge transformation.  In the standard `3+2+1` branch, a gauge
transformation centralizing `SU(3) x SU(2)` has color and weak block phases.
The induced phases on the five chiral Standard Model multiplets are

* `Q`: color plus weak,
* `u^c`: twice color,
* `e^c`: twice weak,
* `d^c`: minus color,
* `L`: minus weak.

This file proves in an arbitrary additive Abelian charge group that both
gauge-mediated proton functionals are unchanged by this twist.  It then
specializes the statement to circle-valued characters of an arbitrary
Abelian residual group, including finite groups, and extracts the two block
characters from the checked actual compact centralizer.  No root of a finite
group character and no decomposition into hypercharge and a complementary
circle is required.
-/

namespace GUT
namespace StandardBlockGaugeCancellation

open WeakDoubletEmbeddingClassification
open ActualCompactCentralizer
open ActualBlockCentralizer
open CompactEmbeddingClassification
open FiniteAbelianChargeSectors
open StandardBranchProtonObstruction
open StandardPhysicalSpectrumBridge

set_option autoImplicit false

noncomputable section

universe u

/-!
## Abstract additive cancellation
-/

/-- Integer color/weak exponents obtained from the conventional generators
`Y5 = (-2,3)` and `X = (1,1)`. -/
def y5xExponentPair (a b : ℤ) : ℤ × ℤ :=
  (-2 * a + b, 3 * a + b)

/-- The `Y5/X` integer lattice consists exactly of block exponent pairs whose
difference is divisible by five. -/
theorem exists_y5xExponentPair_eq_iff (m n : ℤ) :
    (∃ a b : ℤ, y5xExponentPair a b = (m, n)) ↔ 5 ∣ n - m := by
  constructor
  · rintro ⟨a, b, h⟩
    have hColor := congrArg Prod.fst h
    have hWeak := congrArg Prod.snd h
    refine ⟨a, ?_⟩
    simp only [y5xExponentPair] at hColor hWeak
    omega
  · rintro ⟨a, ha⟩
    refine ⟨a, m + 2 * a, ?_⟩
    apply Prod.ext
    · simp [y5xExponentPair]
    · simp only [y5xExponentPair]
      omega

/-- In particular, reducing an arbitrary block lift to integer `Y5/X`
characters is genuinely too strong. -/
theorem no_y5xExponentPair_zero_one :
    ¬ ∃ a b : ℤ, y5xExponentPair a b = (0, 1) := by
  rw [exists_y5xExponentPair_eq_iff]
  norm_num

/-- Add the color and weak block-gauge charges carried by each Standard Model
multiplet to an external charge assignment. -/
def twistCharges
    {A : Type*} [AddCommGroup A] (k : Charges A) (color weak : A) :
    Charges A where
  quark := k.quark + color + weak
  up := k.up + color + color
  down := k.down - color
  lepton := k.lepton - weak
  electron := k.electron + weak + weak

/-- The first proton functional is insensitive to every standard block-gauge
twist. -/
theorem protonFirst_twistCharges
    {A : Type*} [AddCommGroup A] (k : Charges A) (color weak : A) :
    protonFirst (twistCharges k color weak) = protonFirst k := by
  simp only [protonFirst, twistCharges]
  abel

/-- The second proton functional is insensitive to every standard block-gauge
twist. -/
theorem protonSecond_twistCharges
    {A : Type*} [AddCommGroup A] (k : Charges A) (color weak : A) :
    protonSecond (twistCharges k color weak) = protonSecond k := by
  simp only [protonSecond, twistCharges]
  abel

/-- standard charge-orbit bridge may therefore be applied to the gauge-removed external charges: after
an arbitrary block-gauge twist the physical proton functionals still vanish. -/
theorem proton_functionals_eq_zero_of_twist_of_su5OrbitCompatible
    {A : Type*} [AddCommGroup A] (k : Charges A)
    (color weak : A) (hOrbit : SU5OrbitCompatible k) :
    protonFirst (twistCharges k color weak) = 0 ∧
      protonSecond (twistCharges k color weak) = 0 := by
  rw [protonFirst_twistCharges, protonSecond_twistCharges]
  exact proton_functionals_eq_zero_of_su5OrbitCompatible k hOrbit

/-!
## Compact block characters
-/

/-- Color-block projection from the determinant-one compact centralizer. -/
def colorProjection : CompactBlockCentralizer.Group →* Circle where
  toFun p := p.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Weak-block projection from the determinant-one compact centralizer. -/
def weakProjection : CompactBlockCentralizer.Group →* Circle where
  toFun p := p.1.2.1
  map_one' := rfl
  map_mul' _ _ := rfl

def colorCharacter
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) : H →* Circle :=
  colorProjection.comp gauge

def weakCharacter
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) : H →* Circle :=
  weakProjection.comp gauge

def colorCharge
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) : ChargeLabel H :=
  Additive.ofMul (colorCharacter gauge)

def weakCharge
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group) : ChargeLabel H :=
  Additive.ofMul (weakCharacter gauge)

/-- The physical charge assignment obtained by restoring an arbitrary
centralizer-valued block gauge lift. -/
def physicalCharges
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (external : Charges (ChargeLabel H)) : Charges (ChargeLabel H) :=
  twistCharges external (colorCharge gauge) (weakCharge gauge)

theorem protonCharacters_physicalCharges_eq
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (external : Charges (ChargeLabel H)) :
    protonFirstCharacter (physicalCharges gauge external) =
        protonFirstCharacter external ∧
      protonSecondCharacter (physicalCharges gauge external) =
        protonSecondCharacter external := by
  constructor
  · apply Additive.toMul.injective
    exact protonFirst_twistCharges external
      (colorCharge gauge) (weakCharge gauge)
  · apply Additive.toMul.injective
    exact protonSecond_twistCharges external
      (colorCharge gauge) (weakCharge gauge)

/-- An external standard charge-orbit bridge orbit relation makes both physical proton characters
trivial even when the residual representative contains arbitrary color and
weak block-gauge phases. -/
theorem physical_protonCharacters_eq_one_of_su5OrbitCompatible
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (external : Charges (ChargeLabel H))
    (hOrbit : SU5OrbitCompatible external) :
    protonFirstCharacter (physicalCharges gauge external) = 1 ∧
      protonSecondCharacter (physicalCharges gauge external) = 1 := by
  obtain ⟨hFirst, hSecond⟩ :=
    proton_functionals_eq_zero_of_twist_of_su5OrbitCompatible
      external (colorCharge gauge) (weakCharge gauge) hOrbit
  exact ⟨protonFirstCharacter_eq_one_of_eq_zero _ hFirst,
    protonSecondCharacter_eq_one_of_eq_zero _ hSecond⟩

theorem physical_protonPhases_eq_one_of_su5OrbitCompatible
    {H : Type u} [CommGroup H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (external : Charges (ChargeLabel H))
    (hOrbit : SU5OrbitCompatible external) (h : H) :
    protonFirstCharacter (physicalCharges gauge external) h = 1 ∧
      protonSecondCharacter (physicalCharges gauge external) h = 1 := by
  obtain ⟨hFirst, hSecond⟩ :=
    physical_protonCharacters_eq_one_of_su5OrbitCompatible
      gauge external hOrbit
  exact ⟨congrArg (fun chi : H →* Circle => chi h) hFirst,
    congrArg (fun chi : H →* Circle => chi h) hSecond⟩

/-- Explicit finite-Abelian specialization; no divisibility condition on its
character group is used. -/
theorem finiteAbelian_physical_protonCharacters_eq_one
    {H : Type u} [CommGroup H] [Finite H]
    (gauge : H →* CompactBlockCentralizer.Group)
    (external : Charges (ChargeLabel H))
    (hOrbit : SU5OrbitCompatible external) :
    protonFirstCharacter (physicalCharges gauge external) = 1 ∧
      protonSecondCharacter (physicalCharges gauge external) = 1 :=
  physical_protonCharacters_eq_one_of_su5OrbitCompatible
    gauge external hOrbit

/-!
## Extraction from the actual compact centralizer
-/

/-- Bundle an `SU(6)`-valued homomorphism whose image centralizes the actual
semisimple embedding. -/
def toPhysicalCentralizerHom
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota) :
    H →* PhysicalCentralizer iota where
  toFun h := ⟨gauge h, hCentral h⟩
  map_one' := Subtype.ext (map_one gauge)
  map_mul' h k := Subtype.ext (map_mul gauge h k)

/-- The checked compact-centralizer equivalence extracts the determinant-one
block-coefficient homomorphism of any centralizing gauge lift. -/
def actualBlockGaugeHom
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota) :
    H →* CompactBlockCentralizer.Group :=
  (compactBlockCoefficientHom iota W).comp
    (toPhysicalCentralizerHom iota gauge hCentral)

def actualPhysicalCharges
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota)
    (external : Charges (ChargeLabel H)) : Charges (ChargeLabel H) :=
  physicalCharges (actualBlockGaugeHom iota W gauge hCentral) external

/-- Actual centralizer-valued gauge lifts cannot change either proton
selection-rule character obtained from the external standard charge-orbit bridge orbit relation. -/
theorem actualPhysical_protonCharacters_eq_one
    {H : Type u} [CommGroup H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota)
    (external : Charges (ChargeLabel H))
    (hOrbit : SU5OrbitCompatible external) :
    protonFirstCharacter
        (actualPhysicalCharges iota W gauge hCentral external) = 1 ∧
      protonSecondCharacter
        (actualPhysicalCharges iota W gauge hCentral external) = 1 :=
  physical_protonCharacters_eq_one_of_su5OrbitCompatible
    (actualBlockGaugeHom iota W gauge hCentral) external hOrbit

theorem finiteAbelian_actualPhysical_protonCharacters_eq_one
    {H : Type u} [CommGroup H] [Finite H]
    (iota : ProductGroup →* CompactEmbeddingClassification.SU6)
    (W : WeakDoubletData (euclideanDefiningRestriction iota))
    (gauge : H →* CompactEmbeddingClassification.SU6)
    (hCentral : ∀ h, gauge h ∈ PhysicalCentralizer iota)
    (external : Charges (ChargeLabel H))
    (hOrbit : SU5OrbitCompatible external) :
    protonFirstCharacter
        (actualPhysicalCharges iota W gauge hCentral external) = 1 ∧
      protonSecondCharacter
        (actualPhysicalCharges iota W gauge hCentral external) = 1 :=
  actualPhysical_protonCharacters_eq_one
    iota W gauge hCentral external hOrbit

/-!
## Physical sources with a common block-gauge lift

The preceding statements accept the external standard charge-orbit bridge orbit relation as an input.
We now construct that input from the actual gauge-removed character sectors of
a finite physical source.  All summands share one homomorphic gauge lift; this
is the precise source-level condition that they describe one residual
symmetry rather than unrelated transformations on each representation.
-/

/-- One continuous-unitary `SU(6)` matter summand carrying a physical
Abelian action with a specified common gauge lift. -/
structure CommonGaugeSummand
    (H : Type u) [CommGroup H]
    (gauge : H →* CompactEmbeddingClassification.SU6) where
  coeff : ℤ
  rep : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation
  twisted : FiniteResidualActionFactorization.GaugeTwistedAction H rep
  gauge_eq : twisted.gauge = gauge

namespace CommonGaugeSummand

variable {H : Type u} [CommGroup H]
variable {gauge : H →* CompactEmbeddingClassification.SU6}

/-- A unitary semisimple decomposition of the gauge-removed action. -/
def decomposition (s : CommonGaugeSummand H gauge) :
    FiniteSemisimpleDecomposition.Decomposition
      s.twisted.externalRepresentation :=
  Classical.choice (FiniteSemisimpleDecomposition.exists_decomposition
    s.twisted.externalRepresentation
    s.twisted.externalCommutingAction.isSemisimpleRepresentation)

/-- Convert the full external-character sectors of one physical summand into
the finite charged-source format consumed by standard charge-orbit bridge. -/
def toChargedSource (s : CommonGaugeSummand H gauge) :
    StandardPhysicalSource.FiniteChargedContinuousUnitarySource
      (ChargeLabel H) :=
  s.twisted.externalCommutingAction.chargedSectorSource
    s.decomposition s.coeff

/-- The selected sectors recover the original `SU(6)` representation. -/
def sectorRepresentationEquiv (s : CommonGaugeSummand H gauge) :
    Representation.Equiv
      (s.twisted.externalCommutingAction.sectorDirectSumRepresentation
        s.decomposition)
      (ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.rho
        (CommonGaugeSummand.rep s)) :=
  s.twisted.externalCommutingAction.sectorRepresentationEquiv s.decomposition

/-- Forgetting the external charge labels after sector decomposition
recovers the coefficient-weighted restricted character of the original
`SU(6)` summand. -/
theorem toChargedSource_restrictedCharacter_eq
    (s : CommonGaugeSummand H gauge)
    (t : AmbientLaurent.DiagonalPoint) :
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        s.toChargedSource.toVirtual t =
      (s.coeff : ℂ) * ActualRestriction.restrictedCharacter
        (ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.rho
          (CommonGaugeSummand.rep s)) t :=
  s.twisted.externalCommutingAction.chargedSectorSource_restrictedCharacter_eq
    s.decomposition s.coeff t

/-- Removing the common lift and then restoring it recovers the supplied
physical action on every summand. -/
theorem gauge_mul_external_eq_physical
    (s : CommonGaugeSummand H gauge) (h : H) :
    (ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation.rho
        (CommonGaugeSummand.rep s)) (gauge h) *
      s.twisted.externalRepresentation h =
      s.twisted.physical h := by
  have hg : s.twisted.gauge h = gauge h :=
    congrArg (fun f : H →* CompactEmbeddingClassification.SU6 => f h)
      s.gauge_eq
  rw [← hg]
  exact s.twisted.gauge_mul_external_eq_physical h

end CommonGaugeSummand

/-- A finite virtual physical source whose summands share one gauge lift. -/
abbrev CommonGaugeSource
    (H : Type u) [CommGroup H]
    (gauge : H →* CompactEmbeddingClassification.SU6) :=
  List (CommonGaugeSummand H gauge)

namespace CommonGaugeSource

variable {H : Type u} [CommGroup H]
variable {gauge : H →* CompactEmbeddingClassification.SU6}

/-- Collect all full external-character sectors of the physical source. -/
def toChargedSource : CommonGaugeSource H gauge →
    StandardPhysicalSource.FiniteChargedContinuousUnitarySource
      (ChargeLabel H)
  | [] => []
  | s :: source => s.toChargedSource ++ toChargedSource source

/-- The gauge-removed source is chargewise invariant under the standard
`SU(5)` Weyl action. -/
theorem resolvedCharacter_isWeylInvariant
    (source : CommonGaugeSource H gauge) :
    StandardAbelianCharge.ResolvedWeylInvariant
      (source.toChargedSource.resolvedCharacter
        (0 : ℤ →+ ChargeLabel H)) :=
  source.toChargedSource.resolvedCharacter_isWeylInvariant 0

end CommonGaugeSource

/-!
## Strict ordinary Abelian sources

For an ordinary internal symmetry the residual action commutes with the full
`SU(6)` action.  Consequently its common gauge lift is canonically the
identity.  The following conversion removes the gauge-lift premise from the
standard-branch standard charge-orbit bridge source interface in precisely this scope.
-/

/-- One finite-dimensional continuous-unitary `SU(6)` summand with a strict
ordinary Abelian internal action. -/
structure OrdinaryAbelianSummand
    (H : Type u) [CommGroup H] where
  coeff : ℤ
  rep : ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation
  action : FiniteAbelianChargeSectors.CommutingAction H rep

namespace OrdinaryAbelianSummand

variable {H : Type u} [CommGroup H]

/-- Regard a strict ordinary action as a common-gauge summand with the
canonical identity lift. -/
def toCommonGaugeSummand (s : OrdinaryAbelianSummand H) :
    CommonGaugeSummand H
      (1 : H →* CompactEmbeddingClassification.SU6) where
  coeff := s.coeff
  rep := s.rep
  twisted :=
    FiniteResidualActionFactorization.GaugeTwistedAction.ofCommuting s.action
  gauge_eq := rfl

@[simp]
theorem toCommonGaugeSummand_physical
    (s : OrdinaryAbelianSummand H) :
    s.toCommonGaugeSummand.twisted.physical = s.action.rho :=
  rfl

/-- Character-sector decomposition of the converted summand is performed on
the original ordinary Abelian action. -/
theorem toCommonGaugeSummand_externalRepresentation
    (s : OrdinaryAbelianSummand H) :
    s.toCommonGaugeSummand.twisted.externalRepresentation = s.action.rho :=
  FiniteResidualActionFactorization.GaugeTwistedAction.ofCommuting_externalRepresentation
    s.action

end OrdinaryAbelianSummand

/-- A finite virtual source carrying one strict ordinary Abelian action on
each actual continuous-unitary `SU(6)` summand. -/
abbrev OrdinaryAbelianSource
    (H : Type u) [CommGroup H] :=
  List (OrdinaryAbelianSummand H)

namespace OrdinaryAbelianSource

variable {H : Type u} [CommGroup H]

/-- Canonical conversion to the common-gauge source used by standard charge-orbit bridge. -/
def toCommonGaugeSource (source : OrdinaryAbelianSource H) :
    CommonGaugeSource H
      (1 : H →* CompactEmbeddingClassification.SU6) :=
  source.map OrdinaryAbelianSummand.toCommonGaugeSummand

end OrdinaryAbelianSource

/-- Exact SM-only coefficient data for the gauge-removed source.  This is the
source-level standard charge-orbit bridge input before restoring a possibly non-central block-gauge
representative. -/
structure PureSMExternalSpectrumSource
    (H : Type u) [CommGroup H] where
  matter : StandardPhysicalSource.FiniteChargedContinuousUnitarySource
    (ChargeLabel H)
  generations : ℤ
  generations_ne : generations ≠ 0
  externalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  spectrum : IsExactSMOnlyCoefficientSpectrum
    (matter.resolvedCharacter (0 : ℤ →+ ChargeLabel H))
    generations externalCharges singlets

namespace PureSMExternalSpectrumSource

variable {H : Type u} [CommGroup H]

theorem resolvedCharacter_eq_target (S : PureSMExternalSpectrumSource H) :
    S.matter.resolvedCharacter (0 : ℤ →+ ChargeLabel H) =
      StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter
        S.generations S.externalCharges S.singlets :=
  S.spectrum.resolvedCharacter_eq

theorem pureSMChargeSpectrum (S : PureSMExternalSpectrumSource H) :
    StandardAbelianCharge.IsPureSMChargeSpectrum
      (S.matter.resolvedCharacter (0 : ℤ →+ ChargeLabel H))
      S.generations S.externalCharges := by
  rw [S.resolvedCharacter_eq_target]
  exact
    StandardSMCharacterTarget.exactSMWithSingletsResolvedCharacter_isPureSMChargeSpectrum
    S.generations S.externalCharges S.singlets

/-- standard charge-orbit bridge applied to the actual finite-weight character of the gauge-removed
source. -/
theorem su5OrbitCompatible (S : PureSMExternalSpectrumSource H) :
    SU5OrbitCompatible S.externalCharges :=
  StandardAbelianCharge.su5OrbitCompatible_of_pureSM
    (S.matter.resolvedCharacter (0 : ℤ →+ ChargeLabel H))
    (S.matter.resolvedCharacter_isWeylInvariant 0)
    S.generations S.generations_ne S.externalCharges S.pureSMChargeSpectrum

theorem physical_protonCharacters_eq_one
    (S : PureSMExternalSpectrumSource H)
    (gauge : H →* CompactBlockCentralizer.Group) :
    protonFirstCharacter (physicalCharges gauge S.externalCharges) = 1 ∧
      protonSecondCharacter (physicalCharges gauge S.externalCharges) = 1 :=
  physical_protonCharacters_eq_one_of_su5OrbitCompatible
    gauge S.externalCharges S.su5OrbitCompatible

theorem finiteAbelian_physical_protonCharacters_eq_one
    [Finite H] (S : PureSMExternalSpectrumSource H)
    (gauge : H →* CompactBlockCentralizer.Group) :
    protonFirstCharacter (physicalCharges gauge S.externalCharges) = 1 ∧
      protonSecondCharacter (physicalCharges gauge S.externalCharges) = 1 :=
  S.physical_protonCharacters_eq_one gauge

end PureSMExternalSpectrumSource

/-- A physical standard-branch source with one actual centralizing `SU(6)`
gauge lift, together with the explicit coefficient-level SM-only statement
for its gauge-removed character.  `physicalCharges_eq` is the remaining
low-energy interpretation certificate: it identifies the five observed
field characters with the corresponding color/weak block twist. -/
structure PureSMActualBlockGaugeSource
    (H : Type u) [CommGroup H] where
  iota : ProductGroup →* CompactEmbeddingClassification.SU6
  weakDoubletData : WeakDoubletData (euclideanDefiningRestriction iota)
  gauge : H →* CompactEmbeddingClassification.SU6
  gauge_centralizes : ∀ h, gauge h ∈ PhysicalCentralizer iota
  matter : CommonGaugeSource H gauge
  generations : ℤ
  generations_ne : generations ≠ 0
  externalCharges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  externalSpectrum : IsExactSMOnlyCoefficientSpectrum
    (matter.toChargedSource.resolvedCharacter
      (0 : ℤ →+ ChargeLabel H))
    generations externalCharges singlets
  physicalCharges : Charges (ChargeLabel H)
  physicalCharges_eq : physicalCharges =
    actualPhysicalCharges iota weakDoubletData gauge gauge_centralizes
      externalCharges

namespace PureSMActualBlockGaugeSource

variable {H : Type u} [CommGroup H]

def toExternalSpectrumSource (S : PureSMActualBlockGaugeSource H) :
    PureSMExternalSpectrumSource H where
  matter := S.matter.toChargedSource
  generations := S.generations
  generations_ne := S.generations_ne
  externalCharges := S.externalCharges
  singlets := S.singlets
  spectrum := S.externalSpectrum

theorem externalCharge_equalities (S : PureSMActualBlockGaugeSource H) :
    S.externalCharges.quark = S.externalCharges.up ∧
      S.externalCharges.quark = S.externalCharges.electron ∧
      S.externalCharges.down = S.externalCharges.lepton :=
  S.toExternalSpectrumSource.su5OrbitCompatible

/-- Main block-gauge standard charge-orbit bridge to Abelian proton-operator neutrality composition.  It applies to every Abelian
residual group and uses no anomaly equation or divisibility of its character
group. -/
theorem physical_protonCharacters_eq_one
    (S : PureSMActualBlockGaugeSource H) :
    protonFirstCharacter S.physicalCharges = 1 ∧
      protonSecondCharacter S.physicalCharges = 1 := by
  rw [S.physicalCharges_eq]
  exact actualPhysical_protonCharacters_eq_one
    S.iota S.weakDoubletData S.gauge S.gauge_centralizes S.externalCharges
    S.toExternalSpectrumSource.su5OrbitCompatible

theorem physical_protonPhases_eq_one
    (S : PureSMActualBlockGaugeSource H) (h : H) :
    protonFirstCharacter S.physicalCharges h = 1 ∧
      protonSecondCharacter S.physicalCharges h = 1 := by
  obtain ⟨hFirst, hSecond⟩ := S.physical_protonCharacters_eq_one
  exact ⟨congrArg (fun chi : H →* Circle => chi h) hFirst,
    congrArg (fun chi : H →* Circle => chi h) hSecond⟩

theorem finiteAbelian_physical_protonCharacters_eq_one
    [Finite H] (S : PureSMActualBlockGaugeSource H) :
    protonFirstCharacter S.physicalCharges = 1 ∧
      protonSecondCharacter S.physicalCharges = 1 :=
  S.physical_protonCharacters_eq_one

end PureSMActualBlockGaugeSource

end
end StandardBlockGaugeCancellation
end GUT
