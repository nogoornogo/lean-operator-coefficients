import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Counting identities for arbitrary words. Opposite species cancel as
pairs, also in groups with two-torsion; no division by two is used. -/
namespace Math.PatternCountSum
set_option autoImplicit false
open scoped BigOperators
variable {I S A : Type*} [Fintype I] [Fintype S] [DecidableEq S] [AddCommMonoid A]

theorem sum_weights (p : I → S) (w : S → A) :
    ∑ i, w (p i) = ∑ s, (Finset.univ.filter (fun i => p i=s)).card • w s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' (fun i (_ : i ∈ Finset.univ) =>
    Finset.mem_univ (p i)) w]
  simp [Finset.sum_const]

theorem paired_zero {A : Type*} [AddCommGroup A] {r : ℕ}
    (p : I → Fin (r+r)) (w : Fin (r+r) → A)
    (hc : ∀ s : Fin r,
      (Finset.univ.filter (fun i => p i=Fin.castAdd r s)).card =
      (Finset.univ.filter (fun i => p i=Fin.natAdd r s)).card)
    (hw : ∀ s : Fin r, w (Fin.natAdd r s) = -w (Fin.castAdd r s)) :
    ∑ i, w (p i)=0 := by
  classical
  rw [sum_weights,Fin.sum_univ_add,← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro s _
  rw [← hc s,hw s,← nsmul_add,add_neg_cancel,nsmul_zero]

end Math.PatternCountSum
