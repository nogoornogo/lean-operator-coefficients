import Math.RepresentationTheory.InvariantCoefficientProduct
import Math.RepresentationTheory.Decomposition.SplitRepresentationProjection

/-! Restricting a proved finite invariant spanning family to an actual split
source detects support without evaluating a rank or a multiplicity. -/
namespace Math.InvariantSpanningRestriction
set_option autoImplicit false
noncomputable section
open Representation InvariantCoefficientTransport SplitRepresentationProjection

variable {G A B I : Type*} [Group G] [Fintype I]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  {rho : Representation ℂ G A} {sigma : Representation ℂ G B}
  (S : Split rho sigma) (forms : I → Invariants rho)
  (hspan : ∀ f : Invariants rho, ∃ c : I → ℂ, f = ∑ i, c i • forms i)

include hspan in
/-- This helper isolates the remaining algebraic task: deciding which explicit
contraction survives the actual source embedding. -/
theorem allowed_iff : SelectionCriteria.Allowed (Invariants sigma) ↔
    ∃ i, (forms i).comp S.embed ≠ 0 := by
  constructor
  · rintro ⟨f,hf⟩
    by_contra! hn
    obtain ⟨c,hc⟩ := hspan (f.comp S.project)
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change f x = 0
    have he := DFunLike.congr_fun hc (S.embed x)
    change f (S.project (S.embed x)) = _ at he
    rw [S.left_inv] at he
    have hz (i : I) : forms i (S.embed x) = 0 := by
      exact DFunLike.congr_fun (hn i) x
    simpa only [IntertwiningMap.sum_apply,IntertwiningMap.smul_apply,hz,
      smul_zero,Finset.sum_const_zero] using he
  · rintro ⟨i,hi⟩
    exact ⟨(forms i).comp S.embed,hi⟩

end
end Math.InvariantSpanningRestriction
