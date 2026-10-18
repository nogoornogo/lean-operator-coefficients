import GUT.SUN.Branching.DiagonalCharacter
import GUT.SU5.Representations.UnitaryMatter

open Math

/-! Exact restricted characters for the positive SU(7) source
Lambda^2(7) + 3 bar7. Finite enumerations expand traces of actual exterior
powers; they do not replace the representations by prescribed weights. -/

set_option autoImplicit false

namespace GUT.SUN.RankSeven
open Math.SUN


noncomputable section

open SU5.MaximalTorus DiagonalCharacter

def pairsFive : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (2,3), (2,4), (3,4)]

def pairsSeven : Fin 21 → Fin 7 × Fin 7 :=
  ![(0,1), (0,2), (0,3), (0,4), (0,5), (0,6),
    (1,2), (1,3), (1,4), (1,5), (1,6),
    (2,3), (2,4), (2,5), (2,6),
    (3,4), (3,5), (3,6), (4,5), (4,6), (5,6)]

def pairFive (i : Fin 10) : Set.powersetCard (Fin 5) 2 :=
  ⟨{(pairsFive i).1, (pairsFive i).2}, by
    change ({(pairsFive i).1, (pairsFive i).2} : Finset (Fin 5)).card = 2
    fin_cases i <;> decide⟩

def pairSeven (i : Fin 21) : Set.powersetCard (Fin 7) 2 :=
  ⟨{(pairsSeven i).1, (pairsSeven i).2}, by
    change ({(pairsSeven i).1, (pairsSeven i).2} : Finset (Fin 7)).card = 2
    fin_cases i <;> decide⟩

def pairFiveEquiv : Fin 10 ≃ Set.powersetCard (Fin 5) 2 :=
  Equiv.ofBijective pairFive (by
    apply (Fintype.bijective_iff_injective_and_card pairFive).mpr
    refine ⟨by decide, ?_⟩
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, Set.powersetCard.card]
    norm_num [Nat.choose])

def pairSevenEquiv : Fin 21 ≃ Set.powersetCard (Fin 7) 2 :=
  Equiv.ofBijective pairSeven (by
    apply (Fintype.bijective_iff_injective_and_card pairSeven).mpr
    refine ⟨by decide, ?_⟩
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, Set.powersetCard.card]
    norm_num [Nat.choose])

theorem sum_five (z : Fin 5 → ℂ) :
    (∑ s : Set.powersetCard (Fin 5) 2, ∏ i ∈ s.val, z i) =
      ∑ j : Fin 10, z (pairsFive j).1 * z (pairsFive j).2 := by
  rw [← Equiv.sum_comp pairFiveEquiv]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> simp [pairFiveEquiv, pairFive, pairsFive]

theorem sum_seven (z : Fin 7 → ℂ) :
    (∑ s : Set.powersetCard (Fin 7) 2, ∏ i ∈ s.val, z i) =
      ∑ j : Fin 21, z (pairsSeven j).1 * z (pairsSeven j).2 := by
  rw [← Equiv.sum_comp pairSevenEquiv]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> simp [pairSevenEquiv, pairSeven, pairsSeven]

theorem entries_seven (t : Torus) :
    entries 2 t = ![t.val 0, t.val 1, t.val 2, t.val 3, t.val 4, 1, 1] := by
  funext i
  fin_cases i <;> rfl

theorem ten_character (t : Torus) :
    SU5.UnitaryMatter.ten.toRepresentation.character (hom t) =
      ∑ i : Fin 10, (t.val (pairsFive i).1 : ℂ) * (t.val (pairsFive i).2 : ℂ) := by
  rw [← congrFun (Representation.char_iso SU5.UnitaryMatter.tenEquiv) _]
  change LinearMap.trace ℂ _ (exteriorPower.map 2 (Matter.fundamental 5 (hom t))) = _
  exact (ExteriorEigenbasisTrace.exterior_trace (Matter.vectorBasis 5) _ _
    (fundamental_eigen t.val t.property) 2).trans (sum_five _)

theorem bar_five_character (t : Torus) :
    SU5.UnitaryMatter.antifundamental.toRepresentation.character (hom t) =
      ∑ i : Fin 5, (((t.val i)⁻¹ : Circle) : ℂ) := by
  rw [← congrFun (Representation.char_iso SU5.UnitaryMatter.antifundamentalEquiv) _]
  change (Matter.antifundamental 5).character (diagonalElement t.val t.property) = _
  rw [congrFun (Representation.char_iso (Matter.dualEquiv 5)) _]
  exact dual_character _ _

theorem wedge_restriction (t : Torus) :
    (Matter.unitaryWedge 7).toRepresentation.character (Block.inclusion 5 2 (hom t)) =
      SU5.UnitaryMatter.ten.toRepresentation.character (hom t) +
        2 * (∑ i : Fin 5, (t.val i : ℂ)) + 1 := by
  rw [inclusion_diagonal, wedge_character, sum_seven, ten_character, entries_seven]
  simp only [pairsFive, pairsSeven, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  have h5 : ![t.val 0, t.val 1, t.val 2, t.val 3, t.val 4, 1, 1] (5 : Fin 7) = 1 := rfl
  have h6 : ![t.val 0, t.val 1, t.val 2, t.val 3, t.val 4, 1, 1] (6 : Fin 7) = 1 := rfl
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, h5, h6]
  ring!

theorem dual_restriction (t : Torus) :
    (Matter.unitaryDual 7).toRepresentation.character (Block.inclusion 5 2 (hom t)) =
      SU5.UnitaryMatter.antifundamental.toRepresentation.character (hom t) + 2 := by
  rw [inclusion_diagonal, dual_character, bar_five_character, entries_seven]
  simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  ring!

end

end GUT.SUN.RankSeven
