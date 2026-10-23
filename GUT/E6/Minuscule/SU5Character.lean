import GUT.E6.Minuscule.UnitaryRepresentation
import GUT.SU5.Branching.TorusMatterCharacter

open Physics

/-! Actual SU(5) character of the compact candidate's 27 and cancellation
of the vectorlike five/bar-five pair in its dual index. -/

set_option autoImplicit false

namespace GUT.E6.Minuscule

open Math.E6.Minuscule Math.E6
noncomputable section

open GUT.SU5 Physics.SU5 SU5Coordinates TorusMatterCharacter

def dualPairEquiv : Representation.Equiv dualPairRepresentation
    (Matter.antifundamental.prod Matter.antifundamental) :=
  .mk (LinearEquiv.finTwoArrow ℂ Matter.BarFive) (by intro g; ext v <;> rfl)

theorem model_character (g : SU5Coordinates.SU5) :
    modelRepresentation.character g = 2 + Matter.fundamental.character g +
      2 * Matter.antifundamental.character g + Matter.ten.character g := by
  rw [modelRepresentation, character_prod, character_prod, character_prod,
    congrFun (Representation.char_iso dualPairEquiv) g, character_prod]
  have ht : (1 : Representation ℂ SU5Coordinates.SU5 (Fin 2 → ℂ)).character g = 2 := by
    simp [Representation.character]
  rw [ht]
  ring

theorem su5_character (g : SU5Coordinates.SU5) :
    representation.character (inclusion g) = 2 + Matter.fundamental.character g +
      2 * Matter.antifundamental.character g + Matter.ten.character g :=
  (congrFun (Representation.char_iso su5RestrictionEquiv) g).trans (model_character g)

theorem su5_dual_index (g : SU5Coordinates.SU5) :
    representation.character (inclusion g) - representation.dual.character (inclusion g) =
      (UnitaryMatter.ten.toRepresentation.character g -
        UnitaryMatter.ten.toRepresentation.character g⁻¹) +
      (UnitaryMatter.antifundamental.toRepresentation.character g -
        UnitaryMatter.antifundamental.toRepresentation.character g⁻¹) := by
  rw [Representation.char_dual, ← map_inv, su5_character, su5_character,
    ← Representation.char_iso UnitaryMatter.tenEquiv,
    ← Representation.char_iso UnitaryMatter.antifundamentalEquiv]
  simp only [Matter.antifundamental, Representation.char_dual, inv_inv]
  ring

end

end GUT.E6.Minuscule
