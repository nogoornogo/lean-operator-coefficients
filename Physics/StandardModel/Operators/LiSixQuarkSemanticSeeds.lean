import Physics.StandardModel.Operators.LiSixQuarkLocalAction
import Physics.StandardModel.Operators.LiSixQuarkRawSource
import Physics.StandardModel.Operators.LiSixQuarkYoungOperators

/-! Coordinate transport from actual epsilon sources through the factored
Young operators. No evaluated seed-coordinate table is used. -/
namespace GUT.LiSixQuarkSemanticSeeds
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient LiSixQuarkYoungOperators

def coefficientAction (g : Fin 4) : Module.End ℂ Coefficient where
  toFun f := f.domDomCongr (slotSwap g)
  map_add' f h := by ext v; rfl
  map_smul' z f := by ext v; rfl

def seedCoordinates (k : Fin 11) : Fin 5 → Fin 5 → ℂ :=
  young LiSixQuarkLocalAction.action k (LiSixQuarkRawSource.rawCoordinates k)

def seedCoefficient (k : Fin 11) : Coefficient :=
  young coefficientAction k (LiSixQuarkRawSource.rawCoefficient k)

theorem reconstruct_action (g : Fin 4) (c : Fin 5 → Fin 5 → ℂ) :
    reconstruct (LiSixQuarkLocalAction.action g c) = coefficientAction g (reconstruct c) := by
  rw [LiSixQuarkLocalAction.action_actual, reconstruct_transform]
  rfl

theorem seedCoefficient_reconstruct (k : Fin 11) :
    seedCoefficient k = reconstruct (seedCoordinates k) := by
  unfold seedCoefficient seedCoordinates
  rw [LiSixQuarkRawSource.rawCoefficient_reconstruct]
  exact (map_young SixQuarkFlavorCoordinates.reconstructLinear
    LiSixQuarkLocalAction.action coefficientAction reconstruct_action k _).symm

theorem coordinates_seedCoefficient (k : Fin 11) :
    coordinates (seedCoefficient k) = seedCoordinates k := by
  rw [seedCoefficient_reconstruct, coordinates_reconstruct]

end
end GUT.LiSixQuarkSemanticSeeds
