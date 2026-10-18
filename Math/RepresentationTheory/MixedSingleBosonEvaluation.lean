import Math.RepresentationTheory.MixedSingleBosonDescent

/-! Exact one-boson substitution on an exterior coefficient. -/
namespace Math.MixedSingleBosonEvaluation
set_option autoImplicit false
noncomputable section
variable {A B L : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup L] [Module ℂ L] {n : ℕ}

/-- No invariance under transformations moving the substituted boson is asserted. -/
def substitute (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (w : B) : A [⋀^Fin n]→ₗ[ℂ] ℂ :=
  (LinearMap.applyₗ w).compAlternatingMap (MixedSingleBosonDescent.orderedEquiv n f)

theorem substitute_apply (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (w : B) (v : Fin n → A) :
    substitute f w v = f (MixedWeightSupport.pure v (fun _ : Fin 1 => w)) := rfl

theorem substitute_zero (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ) :
    substitute f (0:B) = 0 := by
  ext v
  exact (MixedSingleBosonDescent.orderedEquiv n f v).map_zero

def pull (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (w : B) (j : L →ₗ[ℂ] A) : L [⋀^Fin n]→ₗ[ℂ] ℂ :=
  (substitute f w).compLinearMap j

theorem pull_apply (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (w : B) (j : L →ₗ[ℂ] A) (v : Fin n → L) :
    pull f w j v = f (MixedWeightSupport.pure (j ∘ v) (fun _ : Fin 1 => w)) := rfl

theorem pull_add (f h : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (w : B) (j : L →ₗ[ℂ] A) : pull (f+h) w j = pull f w j + pull h w j := by
  ext v
  rfl

theorem pull_smul (z : ℂ) (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (w : B) (j : L →ₗ[ℂ] A) : pull (z • f) w j = z • pull f w j := by
  ext v
  rfl

theorem pull_zero (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (j : L →ₗ[ℂ] A) : pull f (0:B) j = 0 := by
  unfold pull
  rw [substitute_zero]
  rfl

theorem nonzero_of_probe (f : MixedSingleBosonDescent.Domain (A := A) (B := B) n →ₗ[ℂ] ℂ)
    (w : B) (j : L →ₗ[ℂ] A) (v : Fin n → L)
    (h : f (MixedWeightSupport.pure (j ∘ v) (fun _ : Fin 1 => w)) ≠ 0) :
    pull f w j ≠ 0 := by
  intro hz
  exact h (by simpa only [pull_apply, AlternatingMap.zero_apply] using DFunLike.congr_fun hz v)

variable {G : Type*} [Group G] (a : Representation ℂ G A) (b : Representation ℂ G B)

theorem invariant_at_fixed
    (f : MixedWeightSupport.Coefficient a b (n := n) (m := 1))
    (w : B) (g : G) (hg : b g w = w) (v : Fin n → A) :
    substitute f.toLinearMap w (a g ∘ v) = substitute f.toLinearMap w v := by
  have h := (MixedSingleBosonDescent.extract n a b f).property g v w
  rw [hg] at h
  exact h

end
end Math.MixedSingleBosonEvaluation
