import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Module.Torsion.Free

/-! A nonzero common eigenvector turns pointwise unit phases into a genuine
character. No group law for auxiliary factors is assumed. -/
namespace Math.ScalarEigencharacter
set_option autoImplicit false
noncomputable section
variable {H V : Type*} [Group H] [AddCommMonoid V] [Module ℂ V]

private theorem scalar_injective (v : V) (hv : v ≠ 0) :
    Function.Injective (fun z : ℂ => z • v) := by
  let : AddCommGroup V := Module.addCommMonoidToAddCommGroup ℂ
  exact smul_left_injective ℂ hv

def character (rho : Representation ℂ H V) (phase : H → Circle)
    (v : V) (hne : v ≠ 0) (he : ∀ h, rho h v = (phase h : ℂ) • v) : H →* Circle where
  toFun := phase
  map_one' := by
    apply Subtype.ext
    apply scalar_injective v hne
    simpa using (he 1).symm
  map_mul' h l := by
    apply Subtype.ext
    apply scalar_injective v hne
    have hm := he (h*l)
    rw [rho.map_mul] at hm
    change rho h (rho l v) = _ at hm
    rw [he l, map_smul, he h, smul_smul] at hm
    simpa [mul_comm] using hm.symm

@[simp] theorem character_apply (rho : Representation ℂ H V) (phase : H → Circle)
    (v : V) (hne : v ≠ 0) (he : ∀ h, rho h v = (phase h : ℂ) • v) (h : H) :
    character rho phase v hne he h = phase h := rfl

def onEmbedding {A : Type*} [AddCommMonoid A] [Module ℂ A] [Nontrivial A]
    (rho : Representation ℂ H V) (phase : H → Circle)
    (f : A →ₗ[ℂ] V) (hf : Function.Injective f)
    (he : ∀ h x, rho h (f x) = (phase h : ℂ) • f x) : H →* Circle :=
  let x : A := Classical.choose (exists_ne (0 : A))
  character rho phase (f x)
    (by
      intro hz
      apply Classical.choose_spec (exists_ne (0 : A))
      apply hf
      simpa using hz)
    (fun h => he h x)

@[simp] theorem onEmbedding_apply {A : Type*} [AddCommMonoid A] [Module ℂ A] [Nontrivial A]
    (rho : Representation ℂ H V) (phase : H → Circle)
    (f : A →ₗ[ℂ] V) (hf : Function.Injective f)
    (he : ∀ h x, rho h (f x) = (phase h : ℂ) • f x) (h : H) :
    onEmbedding rho phase f hf he h = phase h := rfl

end
end Math.ScalarEigencharacter
