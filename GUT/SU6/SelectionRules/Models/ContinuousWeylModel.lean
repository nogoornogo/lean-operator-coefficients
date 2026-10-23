import GUT.SU6.SelectionRules.Models.PhysicalWeylZeroModeSupport
import GUT.SU6.SelectionRules.FinalNoGoAssembly

open Physics

/-!
# Continuous geometry and the all-left-handed symmetric mass endpoint

semisimple embedding classification extracts the integral cocharacter from continuous injective geometry.
Canonical nonnegative matter and a symmetric invariant mass supply the dual
index for hypercharge character rigidity -> standard charge-orbit bridge -> Abelian proton-operator neutrality. Actual radical support supplies the operator
signature. This is a finite-dimensional linearized mass model, not a general
Lagrangian/Yukawa semantics or a claim of a nonzero decay amplitude.
-/

set_option autoImplicit false

namespace GUT.ContinuousWeylModel

noncomputable section

open FinalNoGoAssembly PhysicalWeylMassSource PhysicalMassSpectrumBridge
open PhysicalChargeResolvedEvaluation StandardBranchProtonObstruction InvariantWeylMass
open StandardBlockGaugeCancellation (OrdinaryAbelianSource)
open StandardModelLocalOperator WeylConjugateOperator

structure ContinuousWeylMassModel (H : Type*) [CommGroup H] where
  geometry : ContinuousHyperchargeEmbedding
  matter : OrdinaryAbelianSource H
  nonnegative : ∀ s ∈ matter, 0 ≤ s.coeff
  mass : SymmetricMass
    (ordinaryPositiveRepresentation geometry.hyperchargePair.1 geometry.hyperchargePair.2 matter).rho
  generations : ℤ
  generations_ne : generations ≠ 0
  charges : Charges (ChargeLabel H)
  singlets : ChargeLabel H →₀ ℤ
  lightTarget : HasDualSMTarget mass generations charges singlets

namespace ContinuousWeylMassModel

variable {H : Type*} [CommGroup H]

def toPhysical (M : ContinuousWeylMassModel H) : PhysicalWeylModel H where
  colorExponent := M.geometry.hyperchargePair.1
  weakExponent := M.geometry.hyperchargePair.2
  matter := M.matter
  nonnegative := M.nonnegative
  mass := M.mass
  generations := M.generations
  generations_ne := M.generations_ne
  charges := M.charges
  singlets := M.singlets
  lightTarget := M.lightTarget

theorem hyperchargePair_eq_standard (M : ContinuousWeylMassModel H) :
    M.geometry.hyperchargePair = (-2, 3) :=
  Prod.ext M.toPhysical.hypercharge_eq_standard.1 M.toPhysical.hypercharge_eq_standard.2

theorem proton_functionals_eq_zero (M : ContinuousWeylMassModel H) :
    protonFirst M.charges = 0 ∧ protonSecond M.charges = 0 :=
  M.toPhysical.proton_functionals_eq_zero

def supportedInvariantOperator (M : ContinuousWeylMassModel H) (hn : 0 < M.generations) :
    SupportedInvariantOperator (PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical) :=
  PhysicalWeylZeroModeSupport.supportedQque M.toPhysical hn

theorem not_forbidsEverySupportedPhysicalDeltaBOneOperator
    (M : ContinuousWeylMassModel H) (hn : 0 < M.generations) :
    ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator
      (PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical) :=
  (M.supportedInvariantOperator hn).not_forbidsEverySupportedPhysicalDeltaBOneOperator

theorem exists_invariant_operator_or_conjugate (M : ContinuousWeylMassModel H) :
    Nonempty (SupportedInvariantOperator (PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical)) ∨
      Nonempty (SupportedConjugateInvariantOperator
        (PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical)) :=
  PhysicalWeylZeroModeSupport.exists_invariant_operator_or_conjugate M.toPhysical

theorem not_forbidsBothOrientations (M : ContinuousWeylMassModel H) :
    ¬ ForbidsBothOrientations (PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical) :=
  PhysicalWeylZeroModeSupport.not_forbidsBothOrientations M.toPhysical

/-- Finite ordinary residual symmetries require no change to the proof. -/
theorem finiteAbelian_not_forbidsBothOrientations [Finite H] (M : ContinuousWeylMassModel H) :
    ¬ ForbidsBothOrientations (PhysicalWeylZeroModeSupport.lightSpectrum M.toPhysical) :=
  M.not_forbidsBothOrientations

end ContinuousWeylMassModel

end

end GUT.ContinuousWeylModel
