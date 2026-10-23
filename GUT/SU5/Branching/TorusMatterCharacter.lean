import GUT.SU5.Branching.Unitary
import Physics.StandardModel.Spectrum.Representations.GaugeTorusTrace
import GUT.SU5.Embeddings.PhysicalTorus

open Physics

open Math Math.SU5

/-! Trace characters of the retained actual 10 and bar5 on the physical
torus. The full-group branching equivalences supply the character formulas. -/

set_option autoImplicit false

namespace GUT.SU5.TorusMatterCharacter
open Physics.SU5.TorusMatterCharacter
open Physics.SU5

noncomputable section

open StandardSMGaugeTensor StandardModelEmbedding

theorem ten_character (g : GaugeGroup) :
    UnitaryMatter.ten.toRepresentation.character (hom g) =
      phase 4 g⁻¹ * color.character g⁻¹ +
        phase 1 g * (color.character g * weak.character g) + phase (-6) g⁻¹ := by
  have he := congrFun (Representation.char_iso UnitaryBranching.tenEquiv) g
  change UnitaryMatter.ten.toRepresentation.character (hom g) = _ at he
  rw [he, ExteriorSquareBranching.blocksRho, character_prod, character_prod]
  simp only [Representation.char_dual, upRight, quark, electronRight,
    character_twist, Representation.char_tensor, Pi.mul_apply]
  change _ + (_ + phase (-6) g⁻¹ * LinearMap.trace ℂ ℂ LinearMap.id) = _
  simp [add_assoc]

theorem barFive_character (g : GaugeGroup) :
    UnitaryMatter.antifundamental.toRepresentation.character (hom g) =
      phase (-2) g⁻¹ * color.character g⁻¹ + phase 3 g⁻¹ * weak.character g⁻¹ := by
  have he := congrFun (Representation.char_iso UnitaryBranching.antifundamentalEquiv) g
  change UnitaryMatter.antifundamental.toRepresentation.character (hom g) = _ at he
  rw [he]
  rw [← congrFun (Representation.char_iso FundamentalBranching.dualBlocksEquiv) g]
  rw [Representation.char_dual]
  change ((twist color (-2)).prod (twist weak 3)).character g⁻¹ = _
  rw [character_prod, character_twist, character_twist]

open StandardAbelianCharge StandardSMCharacterTarget FiniteAbelianChargeSectors

theorem weighted_character (t : MaximalTorus.Torus) (a b : ℂ) :
    UnitaryMatter.ten.toRepresentation.character (MaximalTorus.hom t) * a +
        UnitaryMatter.antifundamental.toRepresentation.character (MaximalTorus.hom t) * b =
      ∑ i : Fin 15, (TorusCharacter.weightCharacter (smReducedWeight i) t : ℂ) *
        smCharge (sectorCharges a b) i := by
  obtain ⟨z, rfl⟩ := PhysicalTorus.toTorus_surjective t
  rw [← PhysicalTorus.hom_gaugePoint, ten_character, barFive_character,
    color_character, color_character_inv, weak_character, weak_character_inv]
  simp_rw [PhysicalTorus.weightCharacter_toTorus]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, smReducedWeight, smCharge,
    sectorCharges, PhysicalTorus.exponent, phase, PhysicalTorus.gaugePoint]
  have hc : (Circle.coeHom : Circle → ℂ) = (fun a : Circle => (a : ℂ)) := rfl
  simp only [hc]
  field_simp
  ring

theorem charged_pair_character {H : Type*} [CommGroup H] (q r : ChargeLabel H)
    (t : MaximalTorus.Torus) (h : H) :
    UnitaryMatter.ten.toRepresentation.character (MaximalTorus.hom t) * (q.toMul h : ℂ) +
        UnitaryMatter.antifundamental.toRepresentation.character (MaximalTorus.hom t) *
          (r.toMul h : ℂ) =
      TorusCharacter.eval (exactSMResolvedCharacter 1 (sectorCharges q r)) (t, h) := by
  obtain ⟨z, rfl⟩ := PhysicalTorus.toTorus_surjective t
  rw [← PhysicalTorus.hom_gaugePoint, ten_character, barFive_character,
    color_character, color_character_inv, weak_character, weak_character_inv]
  rw [← TorusCharacter.evalAddHom_apply, exactSMResolvedCharacter, map_sum]
  simp only [TorusCharacter.evalAddHom_apply, TorusCharacter.eval_single, Int.cast_one,
    one_mul, smResolvedKey, TorusCharacter.keyCharacter_apply, PhysicalTorus.weightCharacter_toTorus]
  norm_num [Fin.sum_univ_succ, Fin.prod_univ_succ, smReducedWeight, smCharge,
    sectorCharges, PhysicalTorus.exponent, phase, PhysicalTorus.gaugePoint]
  have hc : (Circle.coeHom : Circle → ℂ) = (fun a : Circle => (a : ℂ)) := rfl
  simp only [hc]
  field_simp
  ring

end

end GUT.SU5.TorusMatterCharacter
