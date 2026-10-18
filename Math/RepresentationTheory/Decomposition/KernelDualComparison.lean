import Math.RepresentationTheory.Decomposition.FiniteSummandCancellation
import Math.RepresentationTheory.Decomposition.TensorProductSums

/-! Duals of split kernels are compared by actual source equivalences and
finite-summand cancellation. No irreducible matching premise is required. -/
namespace Math.KernelDualComparison
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection

variable {G A B C D E F : Type*} [Group G]
  [AddCommMonoid A] [Module ℂ A] [AddCommMonoid B] [Module ℂ B]
  [AddCommMonoid C] [Module ℂ C] [AddCommMonoid D] [Module ℂ D]
  [AddCommMonoid E] [Module ℂ E] [AddCommMonoid F] [Module ℂ F]
  {r : Representation ℂ G A} {q : Representation ℂ G B} {k : Representation ℂ G C}
  {s : Representation ℂ G D} {t : Representation ℂ G E} {l : Representation ℂ G F}

def equivalence [Module.Finite ℂ E]
    (e : Representation.Equiv r (q.prod k)) (f : Representation.Equiv s (t.prod l))
    (source : Representation.Equiv r.dual s) (quotient : Representation.Equiv q.dual t) :
    Representation.Equiv k.dual l := by
  letI : AddCommGroup E := Module.addCommMonoidToAddCommGroup ℂ
  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup ℂ
  let whole : Representation.Equiv (t.prod k.dual) (t.prod l) :=
    (prodEquiv quotient.symm (.refl k.dual)).trans
      ((dualProdEquiv q k).trans ((dualEquiv e).symm.trans (source.trans f)))
  exact Classical.choice (FiniteSummandCancellation.nonempty_equiv k.dual l t
    ((TensorProductSums.prodComm k.dual t).trans
      (whole.trans (TensorProductSums.prodComm t l))))

end
end Math.KernelDualComparison
