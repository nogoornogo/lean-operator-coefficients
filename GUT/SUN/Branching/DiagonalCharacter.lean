import Math.LieGroups.SpecialUnitary.Matter
import Math.LinearAlgebra.ExteriorEigenbasisTrace
import GUT.SU5.Embeddings.MaximalTorus

open Math

/-! Characters of actual defining and exterior-square representations on
diagonal SU(n) matrices, including the standard SU(5) block torus. -/

set_option autoImplicit false

namespace GUT.SUN.DiagonalCharacter
open Math.SUN Math.SU5.MaximalTorus


noncomputable section

open SU5.MaximalTorus

theorem fundamental_eigen {n : ℕ} (z : Fin n → Circle) (hz : ∏ i, z i = 1) (i : Fin n) :
    Matter.fundamental n (diagonalElement z hz) (Matter.vectorBasis n i) =
      (z i : ℂ) • Matter.vectorBasis n i := by
  change Matrix.toLin' (Matrix.diagonal (fun j => (z j : ℂ))) (Pi.basisFun ℂ (Fin n) i) = _
  ext j
  by_cases h : j = i <;>
    simp [Matter.vectorBasis, Matrix.toLin'_apply, Matrix.mulVec_diagonal, Pi.basisFun_apply, h]

theorem fundamental_character {n : ℕ} (z : Fin n → Circle) (hz : ∏ i, z i = 1) :
    (Matter.fundamental n).character (diagonalElement z hz) = ∑ i, (z i : ℂ) :=
  ExteriorEigenbasisTrace.trace_eq_sum (Matter.vectorBasis n) _ _ (fundamental_eigen z hz)

theorem dual_character {n : ℕ} (z : Fin n → Circle) (hz : ∏ i, z i = 1) :
    (Matter.unitaryDual n).toRepresentation.character (diagonalElement z hz) =
      ∑ i, (((z i)⁻¹ : Circle) : ℂ) := by
  rw [← congrFun (Representation.char_iso (Matter.dualEquiv n)) _]
  change (Matter.fundamental n).dual.character _ = _
  rw [Representation.char_dual]
  change LinearMap.trace ℂ _ (Matrix.toLin' (star (Matrix.diagonal (fun i => (z i : ℂ))))) = _
  simp only [Matrix.trace_toLin'_eq, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.trace_diagonal, Pi.star_apply, Complex.star_def,
    ← Circle.coe_inv_eq_conj]

theorem wedge_character {n : ℕ} (z : Fin n → Circle) (hz : ∏ i, z i = 1) :
    (Matter.unitaryWedge n).toRepresentation.character (diagonalElement z hz) =
      ∑ s : Set.powersetCard (Fin n) 2, ∏ i ∈ s.val, (z i : ℂ) := by
  rw [← congrFun (Representation.char_iso (Matter.wedgeEquiv n)) _]
  exact ExteriorEigenbasisTrace.exterior_trace (Matter.vectorBasis n) _ _
    (fundamental_eigen z hz) 2

def entries (k : ℕ) (t : Torus) : Fin (5 + k) → Circle :=
  Sum.elim t.val (fun _ => 1) ∘ (Block.indexEquiv 5 k).symm

theorem entries_product (k : ℕ) (t : Torus) : ∏ i, entries k t i = 1 := by
  change (∏ i, Sum.elim t.val (fun _ => 1) ((Block.indexEquiv 5 k).symm i)) = 1
  rw [Equiv.prod_comp]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, mul_one]
  exact t.property

theorem inclusion_diagonal (k : ℕ) (t : Torus) :
    Block.inclusion 5 k (hom t) = diagonalElement (entries k t) (entries_product k t) := by
  apply Subtype.ext
  ext i j
  obtain ⟨i, rfl⟩ := (Block.indexEquiv 5 k).surjective i
  obtain ⟨j, rfl⟩ := (Block.indexEquiv 5 k).surjective j
  change Block.rawMatrix k (hom t)
      ((Block.indexEquiv 5 k).symm (Block.indexEquiv 5 k i))
      ((Block.indexEquiv 5 k).symm (Block.indexEquiv 5 k j)) =
    (Matrix.diagonal (fun i => (entries k t i : ℂ))) (Block.indexEquiv 5 k i) (Block.indexEquiv 5 k j)
  simp only [Equiv.symm_apply_apply, Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]
  cases i <;> cases j <;>
    simp [Block.rawMatrix, hom, diagonalElement, entries, Matrix.diagonal_apply,
      Matrix.one_apply]

end

end GUT.SUN.DiagonalCharacter
