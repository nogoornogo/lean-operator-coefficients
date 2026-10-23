import Math.RepresentationTheory.Decomposition.FiniteBlockHom
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport
import Math.LinearAlgebra.Selection.SelectionCriteria

/-! Support of a finite constituent product, with an arbitrary source. -/
namespace Math.FiniteConstituentSupport
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {G I X : Type*} [Group G] [Fintype I] [DecidableEq I]
  [AddCommGroup X] [Module ℂ X]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (a : Representation ℂ G X) (b : ∀ i, Representation ℂ G (V i))

abbrev Space := InvariantCoefficientTransport.Invariants (a.tprod (FiniteBlockHom.action b))
abbrev Test (i : I) := InvariantCoefficientTransport.Invariants (a.tprod (b i))

def restrict (f : Space a b) (i : I) : Test a b i :=
  f.comp ((FiniteBlockHom.inject b i).lTensor a)
def extend (i : I) (f : Test a b i) : Space a b :=
  f.comp ((FiniteBlockHom.project b i).lTensor a)

omit [Fintype I] in
theorem restrict_extend (i : I) (f : Test a b i) : restrict a b (extend a b i f) i = f := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change f (x ⊗ₜ[ℂ] Pi.single i y i) = f (x ⊗ₜ[ℂ] y)
  simp

theorem eq_zero_of_restrict (f : Space a b) (hf : ∀ i, restrict a b f i = 0) : f=0 := by
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change f (x ⊗ₜ[ℂ] y) = 0
  have hy : (∑ i, Pi.single i (y i)) = y := by ext i; simp
  rw [← hy, TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact DFunLike.congr_fun (hf i) (x ⊗ₜ[ℂ] y i)

theorem allowed_iff : SelectionCriteria.Allowed (Space a b) ↔
    ∃ i, SelectionCriteria.Allowed (Test a b i) := by
  constructor
  · rintro ⟨f,hf⟩
    by_contra hn
    apply hf
    apply eq_zero_of_restrict a b f
    intro i
    by_contra hi
    exact hn ⟨i, restrict a b f i, hi⟩
  · rintro ⟨i,f,hf⟩
    refine ⟨extend a b i f, ?_⟩
    intro he
    have hh := restrict_extend a b i f
    rw [he] at hh
    exact hf hh.symm

end
end Math.FiniteConstituentSupport
