import GUT.SU6.Representations.ConcreteSU6Representations

open Math

/-!
# Concrete character branching for the Dirac benchmark

Compute the restricted trace characters of `6`, `bar6`, and `15` directly
from their algebraic bases, and transfer the answer to the analytic models.
On the standard SU(5) torus, `15 + bar6 - 6` restricts to `10 + bar5`.
-/

namespace GUT.ConcreteSU6Branching

open ConcreteSU6Representations
open AmbientLaurent
open scoped BigOperators

noncomputable section

abbrev DiagonalPoint := ActualRestriction.DiagonalSU6Point

/-- The fifteen ordered pairs indexing a wedge basis of `Lambda^2 C^6`. -/
def pairIndices : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

def wedgePair (i : Fin 15) : Set.powersetCard (Fin 6) 2 :=
  ⟨{(pairIndices i).1, (pairIndices i).2}, by
    change ({(pairIndices i).1, (pairIndices i).2} : Finset (Fin 6)).card = 2
    fin_cases i <;> decide⟩

theorem wedgePair_bijective : Function.Bijective wedgePair := by
  apply (Fintype.bijective_iff_injective_and_card wedgePair).mpr
  constructor
  · decide
  · rw [Fintype.card_fin, Fintype.card_eq_nat_card, Set.powersetCard.card]
    norm_num [Nat.choose]

/-- Enumeration used only to expand a finite, exact trace sum. -/
def wedgePairEquiv : Fin 15 ≃ Set.powersetCard (Fin 6) 2 :=
  Equiv.ofBijective wedgePair wedgePair_bijective

theorem fundamental_diagonal_basis (t : DiagonalPoint) (i : Fin 6) :
    FundamentalRepresentation.rho t.toSU6 (Pi.basisFun ℂ (Fin 6) i) =
      t.coords i • Pi.basisFun ℂ (Fin 6) i := by
  change Matrix.toLin' (Matrix.diagonal t.coords) (Pi.basisFun ℂ (Fin 6) i) = _
  ext j
  by_cases h : j = i <;>
    simp [Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.basisFun_apply, h]

/-- The defining character is the sum of the actual torus coordinates. -/
theorem fundamental_character (t : DiagonalPoint) :
    fundamental.rho.character t.toSU6 = ∑ i, t.coords i := by
  rw [congrFun (Representation.char_iso fundamentalEquiv) t.toSU6]
  exact WeightTheory.trace_eq_sum_of_basis_eigen (Pi.basisFun ℂ (Fin 6))
    (FundamentalRepresentation.rho t.toSU6) t.coords
    (fundamental_diagonal_basis t)

/-- The dual defining character is the sum of inverse torus coordinates. -/
theorem antifundamental_character (t : DiagonalPoint) :
    antifundamental.rho.character t.toSU6 = ∑ i, (t.coords i)⁻¹ := by
  rw [← congrFun (Representation.char_iso antifundamentalEquiv) t.toSU6]
  change FundamentalRepresentation.rho.dual.character t.toSU6 = _
  rw [Representation.char_dual]
  change LinearMap.trace ℂ (Fin 6 → ℂ)
    (Matrix.toLin' (star (Matrix.diagonal t.coords))) = _
  rw [Matrix.trace_toLin'_eq]
  change (∑ i, star (t.coords i)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact eq_inv_of_mul_eq_one_right (AmbientLaurent.DiagonalPoint.coord_mul_star t i)

theorem exterior_diagonal_basis (t : DiagonalPoint)
    (s : Set.powersetCard (Fin 6) 2) :
    exteriorPower.map 2 (FundamentalRepresentation.rho t.toSU6)
        ((Pi.basisFun ℂ (Fin 6)).exteriorPower 2 s) =
      (∏ i ∈ s.val, t.coords i) •
        ((Pi.basisFun ℂ (Fin 6)).exteriorPower 2 s) := by
  let emb := Set.powersetCard.ofFinEmbEquiv.symm s
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
  change exteriorPower.ιMulti ℂ 2
    (fun k => FundamentalRepresentation.rho t.toSU6 (Pi.basisFun ℂ (Fin 6) (emb k))) = _
  simp_rw [fundamental_diagonal_basis]
  rw [AlternatingMap.map_smul_univ]
  rw [CertifiedConstructions.TorusEigenbasis.prod_ofFinEmbEquiv_symm_eq s t.coords]
  rfl

/-- Exterior-square trace as the sum of products of two distinct coordinates. -/
theorem exteriorTwo_character (t : DiagonalPoint) :
    exteriorTwo.rho.character t.toSU6 =
      ∑ i : Fin 15, t.coords (pairIndices i).1 * t.coords (pairIndices i).2 := by
  rw [← congrFun (Representation.char_iso exteriorTwoAlgebraicEquiv) t.toSU6]
  change LinearMap.trace ℂ (⋀[ℂ]^2 (Fin 6 → ℂ))
    (exteriorPower.map 2 (FundamentalRepresentation.rho t.toSU6)) = _
  rw [WeightTheory.trace_eq_sum_of_basis_eigen
    ((Pi.basisFun ℂ (Fin 6)).exteriorPower 2) _
    (fun s => ∏ i ∈ s.val, t.coords i) (exterior_diagonal_basis t)]
  rw [← Equiv.sum_comp wedgePairEquiv]
  apply Finset.sum_congr rfl
  intro i _
  fin_cases i <;> simp [wedgePairEquiv, wedgePair, pairIndices]

/-- The character of `Lambda^2 C^5` in its explicit ten-weight form. -/
def tenValue (z : Fin 6 → ℂ) : ℂ :=
  z 0 * z 1 + z 0 * z 2 + z 0 * z 3 + z 0 * z 4 +
  z 1 * z 2 + z 1 * z 3 + z 1 * z 4 +
  z 2 * z 3 + z 2 * z 4 + z 3 * z 4

/-- Exact standard-block cancellation in the signed benchmark source. -/
theorem signed_character_standard (t : DiagonalPoint) (hLast : t.coords 5 = 1) :
    exteriorTwo.rho.character t.toSU6 +
        antifundamental.rho.character t.toSU6 -
        fundamental.rho.character t.toSU6 =
      tenValue t.coords + ∑ i : Fin 5, (t.coords i.castSucc)⁻¹ := by
  rw [exteriorTwo_character, antifundamental_character, fundamental_character]
  have ht : t.coords =
      ![t.coords 0, t.coords 1, t.coords 2, t.coords 3, t.coords 4, t.coords 5] := by
    funext i
    fin_cases i <;> rfl
  rw [ht]
  have h5 (a b c d e f : ℂ) : ![a, b, c, d, e, f] (5 : Fin 6) = f := rfl
  norm_num [Fin.sum_univ_succ, pairIndices, tenValue, hLast, h5,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

end
end GUT.ConcreteSU6Branching
