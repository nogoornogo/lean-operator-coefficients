import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Invariant evaluation coefficients for arbitrary groups

These are nonzero invariant linear functionals on ordered tensor products,
not claims about light spectra or physical operators modulo statistics.
No commutativity, finiteness or unitarity of the group is required.
-/

set_option autoImplicit false

namespace Math.InvariantPairing

noncomputable section

open scoped TensorProduct

variable {k H V W : Type*} [Field k] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (rho : Representation k H V) (sigma : Representation k H W)

/-- Evaluation is a map of representations to the trivial representation. -/
def evaluation : Representation.IntertwiningMap (rho.tprod rho.dual)
    (Representation.trivial k H k) where
  toLinearMap := contractRight k V
  isIntertwining' g := by
    ext x f
    simp [Representation.tprod_apply, Module.Dual.transpose_apply]

@[simp] theorem evaluation_apply (x : V) (f : Module.Dual k V) :
    evaluation rho (x ⊗ₜ[k] f) = f x := rfl

/-- The ordered factors are `(V, V*, W, W*)`; no alternating quotient is taken. -/
def pairedCoefficient : Representation.IntertwiningMap
    ((rho.tprod rho.dual).tprod (sigma.tprod sigma.dual))
    (Representation.trivial k H k) :=
  (Representation.TensorProduct.lid k (Representation.trivial k H k)).toIntertwiningMap.comp
    ((evaluation rho).tensor (evaluation sigma))

@[simp] theorem pairedCoefficient_apply (x : V) (f : Module.Dual k V)
    (y : W) (l : Module.Dual k W) :
    pairedCoefficient rho sigma ((x ⊗ₜ[k] f) ⊗ₜ[k] (y ⊗ₜ[k] l)) = f x * l y := rfl

theorem pairedCoefficient_invariant (g : H)
    (z : (V ⊗[k] Module.Dual k V) ⊗[k] (W ⊗[k] Module.Dual k W)) :
    pairedCoefficient rho sigma
      (((rho.tprod rho.dual).tprod (sigma.tprod sigma.dual)) g z) =
        pairedCoefficient rho sigma z :=
  congrArg (fun f => f z) ((pairedCoefficient rho sigma).isIntertwining' g)

/-- Nonzeroness is witnessed by a pure tensor, not inferred from equivariance. -/
theorem exists_pairedCoefficient_eq_one [Nontrivial V] [Nontrivial W] :
    ∃ (x : V) (f : Module.Dual k V) (y : W) (l : Module.Dual k W),
      pairedCoefficient rho sigma ((x ⊗ₜ[k] f) ⊗ₜ[k] (y ⊗ₜ[k] l)) = 1 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ := exists_ne (0 : W)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hx
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one k hy
  exact ⟨x, f, y, l, by simp [hf, hl]⟩

theorem pairedCoefficient_ne_zero [Nontrivial V] [Nontrivial W] :
    pairedCoefficient rho sigma ≠ 0 := by
  obtain ⟨x, f, y, l, h⟩ := exists_pairedCoefficient_eq_one rho sigma
  intro hz
  rw [hz] at h
  exact zero_ne_one h

end

end Math.InvariantPairing
