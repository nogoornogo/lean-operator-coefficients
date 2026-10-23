import Math.RepresentationTheory.Content.TripleFlavorCoordinates
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Powerset

/-! Exact cardinalities of the sorted flavor coordinate indices. -/
namespace Math.TripleFlavorCounting
set_option autoImplicit false
noncomputable section

def tripleEmbedding {n : ℕ} (p : TripleMixedCoordinates.TripleIndex n) : Fin 3 ↪o Fin n :=
  OrderEmbedding.ofStrictMono ![p.val.1, p.val.2.1, p.val.2.2] (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals first
      | exact p.property.1
      | exact p.property.2
      | exact lt_trans p.property.1 p.property.2)

def tripleSet {n : ℕ} (p : TripleMixedCoordinates.TripleIndex n) :
    {s : Finset (Fin n) // s.card = 3} :=
  ⟨Finset.univ.map (tripleEmbedding p).toEmbedding, by simp⟩

def setTriple {n : ℕ} (s : {s : Finset (Fin n) // s.card = 3}) :
    TripleMixedCoordinates.TripleIndex n :=
  let e := s.val.orderEmbOfFin s.property
  ⟨(e 0,e 1,e 2), e.strictMono (by decide), e.strictMono (by decide)⟩

theorem setTriple_tripleSet {n : ℕ} (p : TripleMixedCoordinates.TripleIndex n) :
    setTriple (tripleSet p) = p := by
  have he : tripleEmbedding p = (tripleSet p).val.orderEmbOfFin (tripleSet p).property :=
    Finset.orderEmbOfFin_unique' _ (by intro i; simp [tripleSet])
  apply Subtype.ext
  simp only [setTriple, ← he]
  rfl

theorem tripleEmbedding_setTriple {n : ℕ} (s : {s : Finset (Fin n) // s.card = 3}) :
    tripleEmbedding (setTriple s) = s.val.orderEmbOfFin s.property := by
  ext i
  fin_cases i <;> rfl

def tripleEquiv (n : ℕ) : TripleMixedCoordinates.TripleIndex n ≃
    {s : Finset (Fin n) // s.card = 3} where
  toFun := tripleSet
  invFun := setTriple
  left_inv := setTriple_tripleSet
  right_inv s := by
    apply Subtype.ext
    simp only [tripleSet, tripleEmbedding_setTriple, Finset.map_orderEmbOfFin_univ]

theorem triple_card (n : ℕ) :
    Fintype.card (TripleMixedCoordinates.TripleIndex n) = n.choose 3 := by
  rw [Fintype.card_congr (tripleEquiv n), Fintype.card_finset_len, Fintype.card_fin]

def shiftedTriple (n : ℕ) : TripleSymmetricCoordinates.Index n ≃
    TripleMixedCoordinates.TripleIndex (n+2) where
  toFun p := ⟨(⟨p.val.1.val, by omega⟩,
    ⟨p.val.2.1.val+1, by omega⟩, ⟨p.val.2.2.val+2, by omega⟩), by
      have hp := p.property
      change p.val.1.val < p.val.2.1.val + 1 ∧
        p.val.2.1.val + 1 < p.val.2.2.val + 2
      constructor <;> omega⟩
  invFun p := ⟨(⟨p.val.1.val, by
      have hp := p.property; omega⟩,
    ⟨p.val.2.1.val-1, by
      have hp := p.property; omega⟩,
    ⟨p.val.2.2.val-2, by
      have hp := p.property; omega⟩), by
      have hp := p.property
      change p.val.1.val ≤ p.val.2.1.val - 1 ∧
        p.val.2.1.val - 1 ≤ p.val.2.2.val - 2
      constructor <;> omega⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; rfl
    · apply Prod.ext <;> apply Fin.ext <;> simp
  right_inv p := by
    have hp := p.property
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; rfl
    · apply Prod.ext <;> apply Fin.ext <;> dsimp
      all_goals omega

theorem symmetric_card (n : ℕ) :
    Fintype.card (TripleSymmetricCoordinates.Index n) = (n+2).choose 3 := by
  rw [Fintype.card_congr (shiftedTriple n), triple_card]

theorem pair_card (n : ℕ) :
    Fintype.card (TripleMixedCoordinates.PairIndex n) = n*n - n := by
  have he : {p : Fin n × Fin n // p.1 = p.2} ≃ Fin n := {
    toFun := fun p => p.val.1
    invFun := fun i => ⟨(i,i),rfl⟩
    left_inv := by intro p; apply Subtype.ext; exact Prod.ext rfl p.property
    right_inv := by intro i; rfl }
  simp only [TripleMixedCoordinates.PairIndex, Fintype.card_subtype_compl,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_congr he]

/-- A general binomial cardinality formula, including empty flavor spaces. -/
theorem index_card (n : ℕ) :
    Fintype.card (TripleFlavorCoordinates.Index n) =
      (n+2).choose 3 + n.choose 3 + (n*n-n + n.choose 3 * 2) := by
  simp only [TripleFlavorCoordinates.Index, Fintype.card_sum, symmetric_card,
    TripleAlternatingCoordinates.Index, TripleMixedCoordinates.Index,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, triple_card, pair_card]
  omega

end
end Math.TripleFlavorCounting
