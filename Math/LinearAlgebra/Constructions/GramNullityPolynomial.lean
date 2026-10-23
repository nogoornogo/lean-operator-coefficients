import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.Polynomial.Div

/-! A uniform symbolic nullity formula from the Gram characteristic
polynomial. No rank table or individual numerical certificate is consumed. -/
namespace Math.GramNullityPolynomial
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
open scoped ComplexOrder
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def polynomial (A : Matrix I J ℂ) : ℂ[X] := (Aᴴ * A).charpoly

omit [DecidableEq I] in
theorem nullity (A : Matrix I J ℂ) :
    Module.finrank ℂ (LinearMap.ker A.mulVecLin) = (polynomial A).natTrailingDegree := by
  classical
  let B := Aᴴ * A
  have hB : B.IsHermitian := isHermitian_conjTranspose_mul_self A
  have hz : B.charpoly.natTrailingDegree = Fintype.card {i // hB.eigenvalues i = 0} := by
    rw [← Polynomial.rootMultiplicity_eq_natTrailingDegree', ← Polynomial.count_roots,
      hB.roots_charpoly_eq_eigenvalues]
    simp only [Multiset.count_map, Function.comp_apply]
    change (Multiset.filter (fun i => (0 : ℂ) = (hB.eigenvalues i : ℂ)) Finset.univ.val).card = _
    have hp : (fun i => (0 : ℂ) = (hB.eigenvalues i : ℂ)) =
        (fun i => hB.eigenvalues i = 0) := by
      funext i
      apply propext
      norm_cast
      exact eq_comm
    simp only [hp]
    change (Finset.univ.filter (fun i => hB.eigenvalues i = 0)).card = _
    exact (Fintype.card_subtype (fun i => hB.eigenvalues i = 0)).symm
  have hc : Fintype.card {i // hB.eigenvalues i ≠ 0} +
      Fintype.card {i // hB.eigenvalues i = 0} = Fintype.card J := by
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  have hr : A.rank = Fintype.card {i // hB.eigenvalues i ≠ 0} :=
    (rank_conjTranspose_mul_self A).symm.trans hB.rank_eq_card_non_zero_eigs
  have hn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  change A.rank + Module.finrank ℂ (LinearMap.ker A.mulVecLin) = _ at hn
  rw [Module.finrank_fintype_fun_eq_card, hr] at hn
  unfold polynomial
  exact (Nat.add_left_cancel (hn.trans hc.symm)).trans hz.symm

end
end Math.GramNullityPolynomial
