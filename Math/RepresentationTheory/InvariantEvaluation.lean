import Math.RepresentationTheory.InvariantTensorCurry

/-! Dual evaluation turns exhaustive equivariant contractions into exhaustive
invariant functionals without assuming completeness of the latter. -/
namespace Math.InvariantEvaluation
set_option autoImplicit false
noncomputable section
open Representation SplitRepresentationProjection
open scoped TensorProduct

variable {K A B : Type*} [Group K]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [FiniteDimensional ℂ B]
  (a : Representation ℂ K A) (b : Representation ℂ K B)

def equiv : IntertwiningMap (a.tprod b.dual) (Representation.trivial ℂ K ℂ) ≃ₗ[ℂ]
    IntertwiningMap a b :=
  (InvariantTensorCurry.equiv a b.dual).trans
    (InvariantTensorCurry.postcompose a b.dual.dual (bidualEquiv b).symm)

def contraction (p : IntertwiningMap a b) :
    IntertwiningMap (a.tprod b.dual) (Representation.trivial ℂ K ℂ) :=
  (equiv a b).symm p

@[simp] theorem contraction_tmul (p : IntertwiningMap a b) (v : A) (phi : Module.Dual ℂ B) :
    contraction a b p (v ⊗ₜ[ℂ] phi) = phi (p v) := rfl

theorem unique (p : IntertwiningMap a b) (v : A) (phi : Module.Dual ℂ B)
    (hv : phi (p v) = 1) (hp : ∀ f : IntertwiningMap a b, ∃ z : ℂ, f = z • p)
    (f : IntertwiningMap (a.tprod b.dual) (Representation.trivial ℂ K ℂ)) :
    f = f (v ⊗ₜ[ℂ] phi) • contraction a b p := by
  obtain ⟨z, hz⟩ := hp (equiv a b f)
  have hf : f = z • contraction a b p := by
    apply (equiv a b).injective
    simpa [contraction] using hz
  have he : f (v ⊗ₜ[ℂ] phi) = z := by
    rw [hf]
    simp [hv]
  rw [he]
  exact hf

end
end Math.InvariantEvaluation
