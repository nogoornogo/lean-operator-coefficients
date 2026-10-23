import Math.RepresentationTheory.Relations.CommutingStatisticsModule
import Math.RepresentationTheory.Relations.TensorPermutationStatistics
import Math.RepresentationTheory.Constructions.SpechtIsotypicLabels

/-! Nonredundant statistics decomposition of arbitrary flavor tensor powers. -/
namespace Math.TensorStatisticsIsotypic
set_option autoImplicit false
noncomputable section
open Representation
variable {H F W : Type*} [Group H] [AddCommGroup F] [Module ℂ F]
  [AddCommGroup W] [Module ℂ W]
  (a : Representation ℂ H F) (d : ℕ)

private instance cardinalNonzero : NeZero (Nat.card (Equiv.Perm (Fin d)) : ℂ) :=
  ⟨by exact_mod_cast Nat.card_pos.ne'⟩

abbrev statistics := TensorPermutationStatistics.permutation (F := F) d
abbrev commutes := TensorPermutationStatistics.commutes a d
abbrev Index := CommutingStatisticsModule.Index (statistics (F := F) d)
abbrev block := CommutingStatisticsModule.block (a.tensorPower d) (statistics (F := F) d)
  (commutes a d)

def equiv := CommutingStatisticsModule.equiv (a.tensorPower d) (statistics (F := F) d)
  (commutes a d)

/-- A product of residual Homs indexed by distinct nonzero statistics types. -/
def coefficientEquiv (w : Representation ℂ H W) :=
  CommutingStatisticsModule.coefficientEquiv (a.tensorPower d) (statistics (F := F) d)
    (commutes a d) w

def partitionLabel : Index (F := F) d → d.Partition := SpechtIsotypicLabels.label d

theorem partitionLabel_injective : Function.Injective (partitionLabel (F := F) d) :=
  SpechtIsotypicLabels.label_injective d

abbrev Supported := Set.range (partitionLabel (F := F) d)

def supportedEquiv : Index (F := F) d ≃ Supported (F := F) d :=
  SpechtIsotypicLabels.supportedEquiv d

def partitionCoefficientEquiv (w : Representation ℂ H W) :
    IntertwiningMap (a.tensorPower d) w ≃ₗ[ℂ]
      (∀ mu : Supported (F := F) d,
        IntertwiningMap (block a d ((supportedEquiv (F := F) d).symm mu)) w) :=
  (coefficientEquiv a d w).trans
    (LinearEquiv.piCongrLeft' ℂ
      (fun c : Index (F := F) d => IntertwiningMap (block a d c) w)
      (supportedEquiv (F := F) d))

theorem coefficient_zero_iff (w : Representation ℂ H W)
    (f : IntertwiningMap (a.tensorPower d) w) :
    f = 0 ↔ ∀ c, coefficientEquiv a d w f c = 0 :=
  CommutingStatisticsModule.coefficient_zero_iff (a.tensorPower d) (statistics (F := F) d)
    (commutes a d) w f

end
end Math.TensorStatisticsIsotypic
