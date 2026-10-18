import Math.RepresentationTheory.Decomposition.DistinctIrreducibleAssembly
import Math.LinearAlgebra.SelectionCriteria

/-! Homs out of finite products are products of Homs, including arbitrary
reducible summands. This is a finite coproduct fact, not a singlet shortcut. -/
namespace Math.FiniteProductHomSupport
set_option autoImplicit false
noncomputable section
open Representation
variable {G I W : Type*} [Group G] [Fintype I] [DecidableEq I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [AddCommGroup W] [Module ℂ W]
  (a : ∀ i, Representation ℂ G (V i)) (b : Representation ℂ G W)

def equiv : IntertwiningMap (FiniteBlockHom.action a) b ≃ₗ[ℂ]
    (∀ i, IntertwiningMap (a i) b) where
  toFun f i := f.comp (FiniteBlockHom.inject a i)
  invFun := DistinctIrreducibleAssembly.assemble a b
  left_inv f := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change DistinctIrreducibleAssembly.assemble a b
      (fun i => f.comp (FiniteBlockHom.inject a i)) x = f x
    rw [DistinctIrreducibleAssembly.assemble_apply]
    change (∑ i, f (Pi.single i (x i))) = f x
    rw [← map_sum]
    congr 1
    ext i
    simp
  right_inv f := by
    funext i
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact DistinctIrreducibleAssembly.assemble_single a b f i x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem allowed_iff : SelectionCriteria.Allowed (IntertwiningMap (FiniteBlockHom.action a) b) ↔
    ∃ i, SelectionCriteria.Allowed (IntertwiningMap (a i) b) :=
  (SelectionCriteria.allowed_equiv (equiv a b)).trans (SelectionCriteria.allowed_family _)

end
end Math.FiniteProductHomSupport
