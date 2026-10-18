import Physics.StandardModel.Operators.LiSixQuarkFlavorAlternating
import Physics.StandardModel.Operators.DeltaBTwoFlavorBridge

/-! Printed-contraction completeness on down flavor dimension at most three. -/
namespace GUT.LiSixQuarkPrintedCompleteness
noncomputable section
set_option autoImplicit false
open LiSixQuarkFlavorProjection LiSixQuarkFlavorAlternating
open LiSixQuarkExtension LiSixQuarkPrintedSpan SixQuarkTypedFlavor
open SixQuarkFlavorResidualHom

universe u
variable {H : Type*} [Group H]
variable {U D : Type u} [AddCommGroup U] [Module ℂ U]
  [AddCommGroup D] [Module ℂ D]
variable (up : Representation ℂ H U) (down : Representation ℂ H D)

def missingLinear : StatisticsHom U D up down →ₗ[ℂ]
    MultilinearMap ℂ (SlotFlavor U D) ℂ where
  toFun := missing up down
  map_add' k l := by
    ext t
    change extraProbeLinear (homCoordinates _ k.val t + homCoordinates _ l.val t) = _
    exact extraProbeLinear.map_add _ _
  map_smul' z k := by
    ext t
    change extraProbeLinear (z • homCoordinates _ k.val t) = _
    exact extraProbeLinear.map_smul z _

/-- Residual-equivariant Hom with the original four typed statistics equations
and values in the span of printed contractions. No free-flavor claim is made. -/
abbrev PrintedHom := ↥(LinearMap.ker (missingLinear up down))

theorem printedHom_iff (k : StatisticsHom U D up down) :
    k ∈ LinearMap.ker (missingLinear up down) ↔
      ∀ t, homCoordinates (slotRepresentation U D up down) k.val t ∈ printedSpan :=
  missing_zero_iff_printed up down k

def printedEquiv [FiniteDimensional ℂ D] (hd : Module.finrank ℂ D ≤ 3) :
    StatisticsHom U D up down ≃ₗ[ℂ] PrintedHom up down where
  toFun k := ⟨k, missing_zero_of_down_finrank up down hd k⟩
  invFun k := k.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [FiniteDimensional ℂ D]

def physicalEquiv (hd : Module.finrank ℂ D ≤ 3) :
    DeltaBTwoModelInterface.ModelSector up down ≃ₗ[ℂ] PrintedHom up down :=
  (DeltaBTwoFlavorBridge.sectorHomEquiv up down).trans (printedEquiv up down hd)

theorem physical_reconstruction (hd : Module.finrank ℂ D ≤ 3)
    (f : DeltaBTwoModelInterface.ModelSector up down) :
    (physicalEquiv up down hd).symm (physicalEquiv up down hd f) = f :=
  (physicalEquiv up down hd).symm_apply_apply f

theorem physical_extraction (hd : Module.finrank ℂ D ≤ 3)
    (k : PrintedHom up down) :
    physicalEquiv up down hd ((physicalEquiv up down hd).symm k) = k :=
  (physicalEquiv up down hd).apply_symm_apply k

end
end GUT.LiSixQuarkPrintedCompleteness
