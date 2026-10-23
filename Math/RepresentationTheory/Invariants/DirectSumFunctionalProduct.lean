import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Tactic

/-! The algebraic coefficient dual of a direct sum is a product, not a direct sum. -/
namespace Math.DirectSumFunctionalProduct
set_option autoImplicit false
noncomputable section
open Representation
variable {I H : Type*} [DecidableEq I] [Group H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (a : ∀ i, Representation ℂ H (V i))

def inclusion (i : I) : IntertwiningMap (a i) (directSum a) where
  toLinearMap := DirectSum.lof ℂ I V i
  isIntertwining' h := by
    ext x
    simp [Representation.directSum, DirectSum.lmap_lof]

def assemble (f : ∀ i, IntertwiningMap (a i) (trivial ℂ H ℂ)) :
    IntertwiningMap (directSum a) (trivial ℂ H ℂ) where
  toLinearMap := DirectSum.toModule ℂ I ℂ (fun i => (f i).toLinearMap)
  isIntertwining' h := by
    apply DirectSum.linearMap_ext
    intro i
    ext x
    change DirectSum.toModule ℂ I ℂ (fun i => (f i).toLinearMap)
      (DirectSum.lmap (fun i => a i h) (DirectSum.lof ℂ I V i x)) =
      DirectSum.toModule ℂ I ℂ (fun i => (f i).toLinearMap) (DirectSum.lof ℂ I V i x)
    rw [DirectSum.lmap_lof, DirectSum.toModule_lof, DirectSum.toModule_lof]
    exact IntertwiningMap.isIntertwining _ _ (f i) h x

def equiv : IntertwiningMap (directSum a) (trivial ℂ H ℂ) ≃ₗ[ℂ]
    (∀ i, IntertwiningMap (a i) (trivial ℂ H ℂ)) where
  toFun f i := f.comp (inclusion a i)
  invFun := assemble a
  left_inv f := by
    apply IntertwiningMap.ext
    apply DirectSum.linearMap_ext
    intro i
    ext x
    change DirectSum.toModule ℂ I ℂ (fun i =>
      f.toLinearMap.comp (DirectSum.lof ℂ I V i)) (DirectSum.lof ℂ I V i x) =
        f (DirectSum.lof ℂ I V i x)
    rw [DirectSum.toModule_lof]
    rfl
  right_inv f := by
    funext i
    apply IntertwiningMap.ext
    ext x
    change DirectSum.toModule ℂ I ℂ (fun i => (f i).toLinearMap)
      (DirectSum.lof ℂ I V i x) = f i x
    rw [DirectSum.toModule_lof]
    rfl
  map_add' f g := by funext i; apply IntertwiningMap.ext; ext x; rfl
  map_smul' z f := by funext i; apply IntertwiningMap.ext; ext x; rfl

theorem zero_iff (f : IntertwiningMap (directSum a) (trivial ℂ H ℂ)) :
    f = 0 ↔ ∀ i, equiv a f i = 0 := by
  rw [← (equiv a).map_eq_zero_iff]
  exact funext_iff

theorem forbidden_iff :
    (∀ f : IntertwiningMap (directSum a) (trivial ℂ H ℂ), f = 0) ↔
      ∀ i, ∀ f : IntertwiningMap (a i) (trivial ℂ H ℂ), f = 0 := by
  constructor
  · intro h i f
    have he := (equiv a).apply_symm_apply (Pi.single i f)
    have hz := congrArg (fun q => equiv a q i) (h ((equiv a).symm (Pi.single i f)))
    rw [he, (equiv a).map_zero] at hz
    simpa using hz
  · intro h f
    apply (zero_iff a f).mpr
    intro i
    exact h i _

theorem nonzero_iff :
    (∃ f : IntertwiningMap (directSum a) (trivial ℂ H ℂ), f ≠ 0) ↔
      ∃ i, ∃ f : IntertwiningMap (a i) (trivial ℂ H ℂ), f ≠ 0 := by
  simpa only [not_forall, not_not] using not_congr (forbidden_iff a)

end
end Math.DirectSumFunctionalProduct
