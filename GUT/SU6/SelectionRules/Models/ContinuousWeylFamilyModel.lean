import GUT.SU6.SelectionRules.Models.ContinuousWeylYukawaModel
import Physics.FieldTheory.Yukawa.Mass.WeylMassFamilyCompatibility
import Physics.FieldTheory.Yukawa.Mass.MultilinearWeylMassContinuity
import Physics.FieldTheory.Yukawa.Mass.WeylMassPolynomial

open Physics

/-!
# Continuous-geometry models with scalar-dependent symmetric mass sources

The coefficient is jointly continuous and equivariant but need not be
scalar-linear. Finite multilinear sources supply such coefficients. The
mass is derived at a fixed vacuum; the exact dual light target remains an
applicability condition. No scalar potential or decay amplitude is asserted.
The scalar action is on the existing unbroken combined group, not a new
full-SU(6) ultraviolet scalar representation.
-/

set_option autoImplicit false

namespace GUT.ContinuousWeylFamilyModel

noncomputable section

open ContinuousWeylModel PhysicalWeylMassSource PhysicalMassSpectrumBridge
open PhysicalChargeResolvedEvaluation StandardBranchProtonObstruction WeylMassFamily
open UnitaryVirtualRealization FinalNoGoAssembly
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)

structure Model (H : Type*) [CommGroup H] where
  geometry : ContinuousHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  nonnegative : ∀ s ∈ matter, 0 ≤ s.coeff
  scalar : ActualUnitaryGroupRepresentation (CombinedGroup H)
  sector : Sector scalar.rho
    (ordinaryPositiveRepresentation geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  continuous_family : Continuous (fun p : scalar.V × _ × _ =>
    sector.family.toFun p.1 p.2.1 p.2.2)
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

theorem proton_functionals_eq_zero (M : Model H) :
    protonFirst M.charges = 0 ∧ protonSecond M.charges = 0 :=
  M.toMassModel.proton_functionals_eq_zero

def supportedInvariantOperator (M : Model H) (hn : 0 < M.generations) :
    StandardModelLocalOperator.SupportedInvariantOperator
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical) :=
  M.toMassModel.supportedInvariantOperator hn

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator (M : Model H)
    (hn : 0 < M.generations) :
    ¬ StandardModelLocalOperator.ForbidsEverySupportedPhysicalDeltaBOneOperator
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical) :=
  M.toMassModel.not_forbidsEverySupportedPhysicalDeltaBOneOperator hn

theorem not_forbidsBothOrientations (M : Model H) :
    ¬ WeylConjugateOperator.ForbidsBothOrientations
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical) :=
  M.toMassModel.not_forbidsBothOrientations

theorem finiteAbelian_not_forbidsBothOrientations [Finite H] (M : Model H) :
    ¬ WeylConjugateOperator.ForbidsBothOrientations
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical) :=
  M.not_forbidsBothOrientations

/-- No extra continuity certificate is required from a legacy linear model. -/
def ofLinearModel (M : ContinuousWeylYukawaModel.Model H) : Model H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  scalar := M.scalar
  sector := M.sector.toFamilySector
  continuous_family := by
    let := NormedSpace.restrictScalars ℝ ℂ M.scalar.V
    exact M.sector.yukawa.toMultilinearCoupling.continuous_toFamily
      (fun _ => LinearMap.id) (fun _ _ _ => rfl)
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := M.lightTarget

@[simp] theorem ofLinearModel_toMassModel (M : ContinuousWeylYukawaModel.Model H) :
    (ofLinearModel M).toMassModel = M.toMassModel := rfl

@[simp] theorem ofLinearModel_mass (M : ContinuousWeylYukawaModel.Model H) :
    (ofLinearModel M).sector.mass = M.sector.mass := rfl

@[simp] theorem ofLinearModel_lightSpectrum (M : ContinuousWeylYukawaModel.Model H) :
    PhysicalWeylZeroModeSupport.lightSpectrum (ofLinearModel M).toMassModel.toPhysical =
      PhysicalWeylZeroModeSupport.lightSpectrum M.toMassModel.toPhysical := rfl

/-- Neutral power-source realization of an existing mass model, with no bare mass. -/
def ofMassAsPower (M : ContinuousWeylMassModel H) (n : ℕ) : Model H where
  geometry := M.geometry
  matter := M.matter
  nonnegative := M.nonnegative
  scalar := ContinuousWeylYukawaModel.singletScalar (CombinedGroup H)
  sector := Sector.ofMassAsPower M.mass n
  continuous_family := EquivariantFamily.continuous_powerOfMass M.mass n
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := by
    change HasDualSMTarget (Sector.ofMassAsPower M.mass n).mass
      M.generations M.charges M.singlets
    rw [Sector.ofMassAsPower_mass]
    exact M.lightTarget

@[simp] theorem ofMassAsPower_mass (M : ContinuousWeylMassModel H) (n : ℕ) :
    (ofMassAsPower M n).sector.mass = M.mass := Sector.ofMassAsPower_mass M.mass n

@[simp] theorem ofMassAsPower_toMassModel (M : ContinuousWeylMassModel H) (n : ℕ) :
    (ofMassAsPower M n).toMassModel = M := by
  cases M
  dsimp only [ofMassAsPower, toMassModel]
  congr 1
  exact Sector.ofMassAsPower_mass _ _

theorem ofMassAsPower_at_one_nonzero (M : ContinuousWeylMassModel H) (n : ℕ)
    (hM : M.mass.form ≠ 0) : (ofMassAsPower M n).sector.family.toFun (1 : ℂ) ≠ 0 :=
  EquivariantFamily.powerOfMass_nonzero M.mass n hM

theorem ofMassAsPower_quadratic_not_additive (M : ContinuousWeylMassModel H)
    (hM : M.mass.form ≠ 0) :
    (ofMassAsPower M 2).sector.family.Nonadditive :=
  EquivariantFamily.quadratic_nonadditive M.mass hM

theorem ofMassAsPower_zeroVacuum (M : ContinuousWeylMassModel H) (n : ℕ) :
    ({ (ofMassAsPower M (n + 1)).sector with
      vacuum := DiracYukawaMass.InvariantVacuum.zero }).mass =
        InvariantWeylMass.SymmetricMass.zero _ :=
  Sector.ofMassAsPower_zeroVacuum M.mass n

end Model
end
end GUT.ContinuousWeylFamilyModel
