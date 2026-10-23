import Physics.StandardModel.Operators.BaryonTwo.Li.LiSixQuarkPrintedSpan
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkTypedFlavor

/-! Separating character on the genuinely typed residual flavor Hom. -/
namespace Physics.LiSixQuarkFlavorProjection
noncomputable section
open LiSixQuarkExtension LiSixQuarkPrintedSpan SixQuarkFlavorCoordinates
open SixQuarkFlavorResidualHom SixQuarkTypedFlavor SixQuarkSpeciesQuotient

universe u
variable {H : Type*} [Group H]
variable {U D : Type u} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup D] [Module ℂ D]
variable (up : Representation ℂ H U) (down : Representation ℂ H D)

def missing (k : StatisticsHom U D up down) :
    MultilinearMap ℂ (SlotFlavor U D) ℂ :=
  extraProbeLinear.compMultilinearMap (homCoordinates _ k.val)

theorem missing_exchange (k : StatisticsHom U D up down) (g : Fin 4)
    (t : ∀ i, SlotFlavor U D i) :
    missing up down k (exchangeFlavor g (speciesExchange U D g) t) =
      -localSign g * missing up down k t := by
  have he := congrArg extraProbe (k.property g t)
  rw [extraProbe_transform] at he
  change localSign g * missing up down k
      (exchangeFlavor g (speciesExchange U D g) t) =
      extraProbeLinear (-homCoordinates _ k.val t) at he
  rw [map_neg] at he
  change localSign g * missing up down k _ = -missing up down k t at he
  fin_cases g <;> simp [localSign] at he ⊢ <;> linear_combination he

theorem missing_zero_iff_printed (k : StatisticsHom U D up down) :
    missing up down k = 0 ↔
      ∀ t, homCoordinates (slotRepresentation U D up down) k.val t ∈ printedSpan := by
  constructor
  · intro h t
    rw [printedSpan_eq_kernel]
    change missing up down k t = 0
    rw [h]
    rfl
  · intro h
    ext t
    have ht := h t
    rw [printedSpan_eq_kernel] at ht
    exact ht

end
end Physics.LiSixQuarkFlavorProjection
