import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Nonzero scalar coefficients tensor and transport without irreducibility.
Normalized witnesses make positivity constructions explicit. -/
namespace Math.InvariantCoefficientProduct
set_option autoImplicit false
noncomputable section
open Representation InvariantCoefficientTransport
open scoped TensorProduct
variable {G A B : Type*} [Group G] [AddCommMonoid A] [Module ℂ A]
  [AddCommMonoid B] [Module ℂ B]
  (a : Representation ℂ G A) (b : Representation ℂ G B)

def HasUnit : Prop := ∃ f : Invariants a, ∃ x, f x=1

theorem hasUnit_iff : HasUnit a ↔ SelectionCriteria.Allowed (Invariants a) := by
  constructor
  · rintro ⟨f,x,hx⟩
    refine ⟨f,?_⟩
    intro he
    have hz := DFunLike.congr_fun he x
    rw [hx] at hz
    exact one_ne_zero hz
  · rintro ⟨f,hf⟩
    have hx : ∃ x, f x≠0 := by
      by_contra! hx
      apply hf
      ext x
      exact hx x
    obtain ⟨x,hx⟩ := hx
    refine ⟨f,(f x)⁻¹ • x,?_⟩
    rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hx]

variable {a b}

def coefficient (f : Invariants a) (h : Invariants b) : Invariants (a.tprod b) :=
  (Representation.TensorProduct.lid ℂ (trivial ℂ G ℂ)).toIntertwiningMap.comp (f.tensor h)

@[simp] theorem coefficient_pure (f : Invariants a) (h : Invariants b) (x : A) (y : B) :
    coefficient f h (x ⊗ₜ[ℂ] y)=f x*h y := rfl

theorem tensor (ha : HasUnit a) (hb : HasUnit b) : HasUnit (a.tprod b) := by
  obtain ⟨f,x,hx⟩ := ha
  obtain ⟨h,y,hy⟩ := hb
  exact ⟨coefficient f h,x ⊗ₜ[ℂ] y,by rw [coefficient_pure,hx,hy,one_mul]⟩

theorem transport (e : Representation.Equiv a b) (ha : HasUnit a) : HasUnit b := by
  obtain ⟨f,x,hx⟩ := ha
  exact ⟨f.comp e.symm.toIntertwiningMap,e x,by
    change f (e.symm (e x))=1
    rw [e.symm_apply_apply,hx]⟩

end
end Math.InvariantCoefficientProduct
