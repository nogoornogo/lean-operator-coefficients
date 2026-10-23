import GUT.SU6.Characters.ContinuousUnitaryWeightDecomposition
import GUT.SU6.SelectionRules.StandardBranch.StandardAbelianCharge
import Mathlib.Data.Finsupp.SMul

open Physics

open Math

/-!
# Physical charged sources for the standard branch

An ordinary Abelian symmetry can combine a central `U(5)` transformation with
an independent charge carried by each ultraviolet `SU(6)` source multiplet.
Thus the charge of a torus weight is not merely a function of its central
degree: it has the affine form

`sourceOffset + centralCharge totalDegree`.

This file adds that missing source-level datum.  A finite charged source is a
finite virtual collection of actual `SU(6)` representations, each equipped
with an ambient Laurent model and an Abelian source offset.  Its
charge-resolved character is Weyl invariant at every charge, including when
the charge group is finite and different integer lifts collide.  The exact
pure-SM spectrum hypothesis then feeds directly into the anomaly-independent
`standard charge-orbit bridge -> Abelian proton-operator neutrality` proton-functional theorem.
-/

namespace GUT
namespace StandardPhysicalSource

open StandardAbelianCharge
open StandardBranchProtonObstruction

noncomputable section

abbrev RawWeight := StandardAbelianCharge.RawWeight
abbrev RawCharacter := StandardAbelianCharge.RawCharacter
abbrev ResolvedCharacter := StandardAbelianCharge.ResolvedCharacter

/-!
## Affine residual charges
-/

/-- Resolve a standard-branch torus weight when the entire source multiplet
has an additional Abelian charge `offset`. -/
def affineProjectKey {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (e : RawWeight) :
    StandardAbelianCharge.ResolvedKey A :=
  (normalizeWeight e, offset + centralCharge (totalDegree e))

theorem affineProjectKey_permuteWeight
    {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A)
    (sigma : Equiv.Perm (Fin 5)) (e : RawWeight) :
    affineProjectKey centralCharge offset
        (StandardSU5Orbit.permuteWeight sigma e) =
      permuteKey sigma (affineProjectKey centralCharge offset e) := by
  apply Prod.ext
  · exact (permuteReducedWeight_normalizeWeight sigma e).symm
  · change
      offset + centralCharge
          (totalDegree (StandardSU5Orbit.permuteWeight sigma e)) =
        offset + centralCharge (totalDegree e)
    rw [totalDegree_permuteWeight]

/-- Push one finite ambient character to charge-resolved standard-branch
weights, retaining a source-dependent Abelian offset.  `mapDomain` sums all
collisions, so this definition is valid for finite charge groups. -/
def chargeResolvedWithOffset {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (p : RawCharacter) :
    ResolvedCharacter A :=
  Finsupp.mapDomain (affineProjectKey centralCharge offset) p

theorem chargeResolvedWithOffset_isWeylInvariant
    {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (p : RawCharacter)
    (hp : StandardSU5Orbit.WeylInvariant p) :
    ResolvedWeylInvariant
      (chargeResolvedWithOffset centralCharge offset p) := by
  intro sigma
  unfold permuteResolved chargeResolvedWithOffset
  calc
    Finsupp.mapDomain (permuteKey sigma)
          (Finsupp.mapDomain (affineProjectKey centralCharge offset) p) =
        Finsupp.mapDomain
          (permuteKey sigma ∘ affineProjectKey centralCharge offset) p :=
      Finsupp.mapDomain_comp.symm
    _ = Finsupp.mapDomain
          (affineProjectKey centralCharge offset ∘
            StandardSU5Orbit.permuteWeight sigma) p := by
      apply Finsupp.mapDomain_congr
      intro e _he
      exact (affineProjectKey_permuteWeight
        centralCharge offset sigma e).symm
    _ = Finsupp.mapDomain (affineProjectKey centralCharge offset)
          (Finsupp.mapDomain
            (StandardSU5Orbit.permuteWeight sigma) p) :=
      Finsupp.mapDomain_comp
    _ = Finsupp.mapDomain (affineProjectKey centralCharge offset) p := by
      rw [show Finsupp.mapDomain
          (StandardSU5Orbit.permuteWeight sigma) p = p from hp sigma]

theorem affineProjectKey_tenQ
    {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (k : ℤ) :
    affineProjectKey centralCharge offset (StandardSU5Orbit.tenQ k) =
      (reducedTenQ, offset + centralCharge (5 * k + 2)) := by
  rw [affineProjectKey, normalizeWeight_tenQ, totalDegree_tenQ]

theorem affineProjectKey_tenUp
    {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (k : ℤ) :
    affineProjectKey centralCharge offset (StandardSU5Orbit.tenUp k) =
      (reducedTenUp, offset + centralCharge (5 * k + 2)) := by
  rw [affineProjectKey, normalizeWeight_tenUp, totalDegree_tenUp]

theorem affineProjectKey_tenElectron
    {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (k : ℤ) :
    affineProjectKey centralCharge offset
        (StandardSU5Orbit.tenElectron k) =
      (reducedTenElectron, offset + centralCharge (5 * k + 2)) := by
  rw [affineProjectKey, normalizeWeight_tenElectron,
    totalDegree_tenElectron]

theorem affineProjectKey_barFiveDown
    {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (k : ℤ) :
    affineProjectKey centralCharge offset
        (StandardSU5Orbit.barFiveDown k) =
      (reducedBarFiveDown, offset + centralCharge (5 * k - 1)) := by
  rw [affineProjectKey, normalizeWeight_barFiveDown,
    totalDegree_barFiveDown]

theorem affineProjectKey_barFiveLepton
    {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) (offset : A) (k : ℤ) :
    affineProjectKey centralCharge offset
        (StandardSU5Orbit.barFiveLepton k) =
      (reducedBarFiveLepton, offset + centralCharge (5 * k - 1)) := by
  rw [affineProjectKey, normalizeWeight_barFiveLepton,
    totalDegree_barFiveLepton]

/-!
## Finite charged actual sources
-/

/-- One finite virtual `SU(6)` summand, with its checked Laurent realization
and the independent Abelian charge of its ultraviolet source multiplet. -/
structure ChargedModeledVirtualSummand (A : Type*) where
  modeled : AmbientCharacterBridge.ModeledVirtualSummand
  offset : A

namespace ChargedModeledVirtualSummand

def toVirtualSummand {A : Type*}
    (s : ChargedModeledVirtualSummand A) :
    AmbientCharacterBridge.VirtualSummand :=
  s.modeled.toVirtualSummand

/-- Recover the actual-character certificate carried by the modeled
summand. -/
def actualModel {A : Type*} (s : ChargedModeledVirtualSummand A) :
    AmbientCharacterBridge.ActualAmbientLaurentModel s.modeled.rep.rho where
  poly := s.modeled.poly
  evaluates_character := s.modeled.evaluates_rep

/-- The charge-resolved chiral character contributed by one source summand. -/
def resolved {A : Type*} [AddCommGroup A]
    (s : ChargedModeledVirtualSummand A)
    (centralCharge : ℤ →+ A) : ResolvedCharacter A :=
  s.modeled.coeff •
    chargeResolvedWithOffset centralCharge s.offset s.modeled.poly

theorem resolved_isWeylInvariant
    {A : Type*} [AddCommGroup A]
    (s : ChargedModeledVirtualSummand A)
    (centralCharge : ℤ →+ A) :
    ResolvedWeylInvariant (s.resolved centralCharge) := by
  have hBase : ResolvedWeylInvariant
      (chargeResolvedWithOffset centralCharge s.offset s.modeled.poly) :=
    chargeResolvedWithOffset_isWeylInvariant
      centralCharge s.offset s.modeled.poly
      (standardWeylInvariant_of_ambient s.modeled.poly s.actualModel.isWeylInvariant)
  intro sigma
  have hBaseSigma := hBase sigma
  unfold permuteResolved at hBaseSigma
  unfold resolved permuteResolved
  rw [Finsupp.mapDomain_smul, hBaseSigma]

end ChargedModeledVirtualSummand

abbrev FiniteChargedModeledVirtualSource (A : Type*) :=
  List (ChargedModeledVirtualSummand A)

namespace FiniteChargedModeledVirtualSource

/-- Forget only the Abelian offsets, retaining every modeled virtual
summand. -/
def forgetCharges {A : Type*} :
    FiniteChargedModeledVirtualSource A →
      AmbientCharacterBridge.ModeledFiniteVirtualRepresentation
  | [] => []
  | s :: ss => s.modeled :: forgetCharges ss

def toVirtual {A : Type*} :
    FiniteChargedModeledVirtualSource A →
      AmbientCharacterBridge.FiniteVirtualRepresentation
  | [] => []
  | s :: ss => s.toVirtualSummand :: toVirtual ss

@[simp]
theorem forgetCharges_toVirtual {A : Type*}
    (source : FiniteChargedModeledVirtualSource A) :
    AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtual
        source.forgetCharges = source.toVirtual := by
  induction source with
  | nil => rfl
  | cons s ss ih =>
      simp [forgetCharges,
        AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.toVirtual,
        toVirtual, ChargedModeledVirtualSummand.toVirtualSummand, ih]

/-- Sum the charge-resolved chiral characters of all ultraviolet source
multiplets. -/
def resolvedCharacter {A : Type*} [AddCommGroup A]
    (centralCharge : ℤ →+ A) :
    FiniteChargedModeledVirtualSource A → ResolvedCharacter A
  | [] => 0
  | s :: ss => s.resolved centralCharge + resolvedCharacter centralCharge ss

theorem resolvedCharacter_isWeylInvariant
    {A : Type*} [AddCommGroup A]
    (source : FiniteChargedModeledVirtualSource A)
    (centralCharge : ℤ →+ A) :
    ResolvedWeylInvariant (resolvedCharacter centralCharge source) := by
  induction source with
  | nil =>
      intro sigma
      simp [resolvedCharacter, permuteResolved]
  | cons s ss ih =>
      intro sigma
      have hs := s.resolved_isWeylInvariant centralCharge sigma
      have hss := ih sigma
      unfold permuteResolved at hs hss
      unfold resolvedCharacter permuteResolved
      rw [Finsupp.mapDomain_add, hs, hss]

end FiniteChargedModeledVirtualSource

/-!
## Construction from continuous unitary representations
-/

abbrev ContinuousUnitaryRepresentation :=
  ContinuousUnitaryWeightDecomposition.ContinuousUnitarySU6Representation

/-- A physically scoped finite-dimensional continuous unitary `SU(6)` source
multiplet, with virtual chiral coefficient and Abelian source charge. -/
structure ChargedContinuousUnitarySummand (A : Type*) where
  coeff : ℤ
  rep : ContinuousUnitaryRepresentation
  offset : A

namespace ChargedContinuousUnitarySummand

def toModeled {A : Type*} (s : ChargedContinuousUnitarySummand A) :
    ChargedModeledVirtualSummand A where
  modeled :=
    { coeff := s.coeff
      rep := s.rep.toActualRepresentation
      poly := s.rep.ambientLaurentModel.poly
      evaluates_rep := s.rep.ambientLaurentModel.evaluates_character }
  offset := s.offset

end ChargedContinuousUnitarySummand

abbrev FiniteChargedContinuousUnitarySource (A : Type*) :=
  List (ChargedContinuousUnitarySummand A)

namespace FiniteChargedContinuousUnitarySource

def toModeled {A : Type*} :
    FiniteChargedContinuousUnitarySource A →
      FiniteChargedModeledVirtualSource A
  | [] => []
  | s :: ss => s.toModeled :: toModeled ss

/-- Forget the Abelian charge labels while retaining the underlying finite
virtual `SU(6)` representation. -/
def toVirtual {A : Type*}
    (source : FiniteChargedContinuousUnitarySource A) :
    AmbientCharacterBridge.FiniteVirtualRepresentation :=
  FiniteChargedModeledVirtualSource.toVirtual source.toModeled

/-- The common normalized ambient Laurent model of the underlying actual
finite virtual `SU(6)` source. -/
def ambientLaurentModel {A : Type*}
    (source : FiniteChargedContinuousUnitarySource A) :
    AmbientCharacterBridge.VirtualAmbientLaurentModel source.toVirtual where
  poly := AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.poly
    source.toModeled.forgetCharges
  evaluates_character t := by
    rw [AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.poly_evaluates]
    exact congrArg
      (fun chi => AmbientCharacterBridge.finiteVirtualRestrictedCharacter chi t)
      (FiniteChargedModeledVirtualSource.forgetCharges_toVirtual source.toModeled)

theorem ambientLaurentModel_poly {A : Type*}
    (source : FiniteChargedContinuousUnitarySource A) :
    source.ambientLaurentModel.poly =
      AmbientCharacterBridge.ModeledFiniteVirtualRepresentation.poly
        source.toModeled.forgetCharges :=
  rfl

/-- Forgetting charge labels turns the virtual restricted character into the
finite sum of the coefficient-weighted actual traces of the source
summands. -/
theorem finiteVirtualRestrictedCharacter_toVirtual_eq_sum
    {A : Type*} (source : FiniteChargedContinuousUnitarySource A)
    (t : AmbientLaurent.DiagonalPoint) :
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        source.toVirtual t =
      (source.map fun s =>
        (s.coeff : ℂ) * ActualRestriction.restrictedCharacter s.rep.rho t).sum := by
  induction source with
  | nil => rfl
  | cons s source ih =>
      change
        (s.coeff : ℂ) * ActualRestriction.restrictedCharacter s.rep.rho t +
            AmbientCharacterBridge.finiteVirtualRestrictedCharacter
              (FiniteChargedContinuousUnitarySource.toVirtual source) t =
          (s.coeff : ℂ) * ActualRestriction.restrictedCharacter s.rep.rho t +
            (source.map fun r =>
              (r.coeff : ℂ) *
                ActualRestriction.restrictedCharacter r.rep.rho t).sum
      rw [ih]

/-- Forgetting charges commutes with concatenation at the level of the
restricted virtual character. -/
theorem finiteVirtualRestrictedCharacter_toVirtual_append
    {A : Type*} (left right : FiniteChargedContinuousUnitarySource A)
    (t : AmbientLaurent.DiagonalPoint) :
    AmbientCharacterBridge.finiteVirtualRestrictedCharacter
        (FiniteChargedContinuousUnitarySource.toVirtual (left ++ right)) t =
      AmbientCharacterBridge.finiteVirtualRestrictedCharacter
          (FiniteChargedContinuousUnitarySource.toVirtual left) t +
        AmbientCharacterBridge.finiteVirtualRestrictedCharacter
          (FiniteChargedContinuousUnitarySource.toVirtual right) t := by
  rw [finiteVirtualRestrictedCharacter_toVirtual_eq_sum,
    finiteVirtualRestrictedCharacter_toVirtual_eq_sum,
    finiteVirtualRestrictedCharacter_toVirtual_eq_sum,
    List.map_append, List.sum_append]

def resolvedCharacter {A : Type*} [AddCommGroup A]
    (source : FiniteChargedContinuousUnitarySource A)
    (centralCharge : ℤ →+ A) : ResolvedCharacter A :=
  FiniteChargedModeledVirtualSource.resolvedCharacter centralCharge
    source.toModeled

theorem resolvedCharacter_isWeylInvariant
    {A : Type*} [AddCommGroup A]
    (source : FiniteChargedContinuousUnitarySource A)
    (centralCharge : ℤ →+ A) :
    ResolvedWeylInvariant (source.resolvedCharacter centralCharge) :=
  FiniteChargedModeledVirtualSource.resolvedCharacter_isWeylInvariant
    source.toModeled centralCharge

end FiniteChargedContinuousUnitarySource

/-!
## Exact physical spectrum and the main standard charge-orbit bridge to Abelian proton-operator neutrality route
-/

/-- A finite continuous-unitary ultraviolet source together with the exact
charge-resolved SM-only chiral-spectrum statement needed by standard charge-orbit bridge.  The charge
group may be continuous or finite; no anomaly condition is included. -/
structure PureSMChargedSource (A : Type*) [AddCommGroup A] where
  matter : FiniteChargedContinuousUnitarySource A
  centralCharge : ℤ →+ A
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges A
  spectrum : IsPureSMChargeSpectrum
    (matter.resolvedCharacter centralCharge) generations charges

namespace PureSMChargedSource

/-- Main standard-branch source theorem: an exact physical charged source
satisfying the SM-only chiral-spectrum hypothesis has neutral proton
functionals.  This is `standard charge-orbit bridge -> Abelian proton-operator neutrality` and uses no anomaly equation. -/
theorem proton_functionals_eq_zero
    {A : Type*} [AddCommGroup A] (S : PureSMChargedSource A) :
    protonFirst S.charges = 0 ∧ protonSecond S.charges = 0 := by
  apply StandardAbelianCharge.proton_functionals_eq_zero_of_pureSM
    (S.matter.resolvedCharacter S.centralCharge)
    (S.matter.resolvedCharacter_isWeylInvariant S.centralCharge)
    S.generations S.generations_ne S.charges S.spectrum

/-- The same theorem stated explicitly for a finite Abelian charge group. -/
theorem finiteAbelian_proton_functionals_eq_zero
    {A : Type*} [AddCommGroup A] [Finite A]
    (S : PureSMChargedSource A) :
    protonFirst S.charges = 0 ∧ protonSecond S.charges = 0 :=
  S.proton_functionals_eq_zero

/-- Concrete finite-cyclic specialization. -/
theorem cyclic_proton_functionals_eq_zero
    {N : ℕ} [NeZero N] (S : PureSMChargedSource (ZMod N)) :
    protonFirst S.charges = 0 ∧ protonSecond S.charges = 0 :=
  S.proton_functionals_eq_zero

end PureSMChargedSource

/-- The weaker family-dependent physical input: both the `10` and
anti-fundamental SM orbit profiles occur somewhere in the charged chiral
spectrum. -/
structure OccupiedSMChargedSource (A : Type*) [AddCommGroup A] where
  matter : FiniteChargedContinuousUnitarySource A
  centralCharge : ℤ →+ A
  ten_nonzero :
    quarkProfile (matter.resolvedCharacter centralCharge) ≠ 0
  barFive_nonzero :
    downProfile (matter.resolvedCharacter centralCharge) ≠ 0

namespace OccupiedSMChargedSource

/-- The family-dependent standard charge-orbit bridge-to-Abelian proton-operator neutrality conclusion at character level: there are
occupied common-charge sectors containing all five required SM field types,
and both proton functionals are neutral on those sectors. -/
theorem exists_supported_neutral_proton_sectors
    {A : Type*} [AddCommGroup A] (S : OccupiedSMChargedSource A) :
    ∃ k : Charges A,
      ChargesSupported
          (S.matter.resolvedCharacter S.centralCharge) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 := by
  apply StandardAbelianCharge.exists_supported_neutral_proton_sectors
    (S.matter.resolvedCharacter S.centralCharge)
    (S.matter.resolvedCharacter_isWeylInvariant S.centralCharge)
    S.ten_nonzero S.barFive_nonzero

/-- Explicit finite-Abelian specialization of the occupied-sector result. -/
theorem finiteAbelian_exists_supported_neutral_proton_sectors
    {A : Type*} [AddCommGroup A] [Finite A]
    (S : OccupiedSMChargedSource A) :
    ∃ k : Charges A,
      ChargesSupported
          (S.matter.resolvedCharacter S.centralCharge) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 :=
  S.exists_supported_neutral_proton_sectors

/-- Concrete finite-cyclic specialization of the occupied-sector result. -/
theorem cyclic_exists_supported_neutral_proton_sectors
    {N : ℕ} [NeZero N] (S : OccupiedSMChargedSource (ZMod N)) :
    ∃ k : Charges (ZMod N),
      ChargesSupported
          (S.matter.resolvedCharacter S.centralCharge) k ∧
        protonFirst k = 0 ∧ protonSecond k = 0 :=
  S.exists_supported_neutral_proton_sectors

end OccupiedSMChargedSource

end
end StandardPhysicalSource
end GUT
