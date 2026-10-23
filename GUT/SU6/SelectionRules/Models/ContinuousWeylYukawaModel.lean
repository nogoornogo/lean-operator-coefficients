import GUT.SU6.SelectionRules.Models.ContinuousWeylModel
import Physics.FieldTheory.Yukawa.Mass.WeylYukawaMass

open Physics

/-!
# Continuous-geometry Weyl models with primitive Yukawa and vacuum data

The linearized mass is derived from a symmetric scalar-linear coupling and
an invariant VEV. The exact radical dual target is still an applicability
condition. This does not define a general Lagrangian or a scalar potential.
-/

set_option autoImplicit false

namespace GUT.ContinuousWeylYukawaModel

noncomputable section

open ContinuousWeylModel PhysicalWeylMassSource PhysicalMassSpectrumBridge
open PhysicalChargeResolvedEvaluation StandardBranchProtonObstruction WeylYukawaMass
open UnitaryVirtualRealization FinalNoGoAssembly
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)

structure Model (H : Type*) [CommGroup H] where
  geometry : ContinuousHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  nonnegative : ∀ s ∈ matter, 0 ≤ s.coeff
  scalar : ActualUnitaryGroupRepresentation (CombinedGroup H)
  sector : Sector scalar.rho
    (ordinaryPositiveRepresentation geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : HasDualSMTarget sector.mass generations charges singlets

variable {H : Type*} [CommGroup H]

namespace Model

def toMassModel (M : Model H) : ContinuousWeylMassModel H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  mass := M.sector.mass
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := M.lightTarget

theorem hyperchargePair_eq_standard (M : Model H) : M.geometry.hyperchargePair = (-2, 3) :=
  M.toMassModel.hyperchargePair_eq_standard

def supportedInvariantOperator (M : Model H) (hn : 0 < M.generations) :
    StandardModelLocalOperator.SupportedInvariantOperator
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical) :=
  M.toMassModel.supportedInvariantOperator hn

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator (M : Model H) (hn : 0 < M.generations) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical) :=
  M.toMassModel.not_forbidsEverySupportedPhysicalDeltaBOneOperator hn

theorem not_forbidsBothOrientations (M : Model H) :
    ¬ WeylConjugateOperator.ForbidsBothOrientations
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical) :=
  M.toMassModel.not_forbidsBothOrientations

def ofBareMassModel (M : ContinuousWeylMassModel H)
    (scalar : ActualUnitaryGroupRepresentation (CombinedGroup H)) : Model H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  scalar := scalar
  sector := Sector.ofBareMass M.mass
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := by simpa using M.lightTarget

theorem ofBareMassModel_mass (M : ContinuousWeylMassModel H)
    (scalar : ActualUnitaryGroupRepresentation (CombinedGroup H)) :
    (ofBareMassModel M scalar).sector.mass = M.mass := Sector.ofBareMass_mass M.mass

end Model

/-- An actual neutral one-dimensional scalar, used only for compatibility examples. -/
def singletScalar (G : Type*) [Group G] : ActualUnitaryGroupRepresentation G where
  V := ℂ
  rho := Representation.trivial ℂ G ℂ
  unitary := by intro g x y; rfl

namespace Model

def ofMassAsYukawa (M : ContinuousWeylMassModel H) : Model H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  scalar := singletScalar (CombinedGroup H)
  sector := Sector.ofMassAsYukawa M.mass
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := by
    change HasDualSMTarget (Sector.ofMassAsYukawa M.mass).mass M.generations M.charges M.singlets
    rw [Sector.ofMassAsYukawa_mass]
    exact M.lightTarget

theorem ofMassAsYukawa_mass (M : ContinuousWeylMassModel H) :
    (ofMassAsYukawa M).sector.mass = M.mass := Sector.ofMassAsYukawa_mass M.mass

theorem ofMassAsYukawa_toMassModel (M : ContinuousWeylMassModel H) :
    (ofMassAsYukawa M).toMassModel = M := by
  cases M
  dsimp only [ofMassAsYukawa, toMassModel]
  congr 1
  exact Sector.ofMassAsYukawa_mass _

end Model

end

end GUT.ContinuousWeylYukawaModel
