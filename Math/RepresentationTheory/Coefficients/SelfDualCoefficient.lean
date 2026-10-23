import Math.RepresentationTheory.Exterior.ComplementaryExteriorDuality
import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! A self-dual source turns an actual constituent map into a nonzero coefficient. -/
namespace Math.SelfDualCoefficient
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G A B : Type*} [Group G] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B)

def map (e : Representation.Equiv a a.dual) (f : IntertwiningMap b a) :
    InvariantCoefficientTransport.Invariants (a.tprod b) :=
  InvariantTensorCurry.uncurry a b
    ((SplitRepresentationProjection.dualMap f).comp e.toIntertwiningMap)

@[simp] theorem apply (e : Representation.Equiv a a.dual) (f : IntertwiningMap b a)
    (x : A) (y : B) : map a b e f (x ⊗ₜ[ℂ] y) = e x (f y) := rfl

theorem nonzero (e : Representation.Equiv a a.dual) (f : IntertwiningMap b a)
    (hf : f ≠ 0) : map a b e f ≠ 0 := by
  have hx : ∃ x, f x ≠ 0 := by
    by_contra h
    apply hf
    ext x
    exact not_not.mp (not_exists.mp h x)
  obtain ⟨x,hx⟩ := hx
  obtain ⟨phi,hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  intro h
  have he := DFunLike.congr_fun h (e.symm phi ⊗ₜ[ℂ] x)
  change e (e.symm phi) (f x) = 0 at he
  rw [e.apply_symm_apply, hphi] at he
  exact one_ne_zero he

theorem allowed (e : Representation.Equiv a a.dual) [Nontrivial B]
    (f : IntertwiningMap b a) (hf : Function.Injective f) :
    SelectionCriteria.Allowed (InvariantCoefficientTransport.Invariants (a.tprod b)) := by
  have hn : f ≠ 0 := by
    intro h
    obtain ⟨x,hx⟩ := exists_ne (0 : B)
    apply hx
    apply hf
    rw [h]
    rfl
  exact ⟨map a b e f, nonzero a b e f hn⟩

end
end Math.SelfDualCoefficient
