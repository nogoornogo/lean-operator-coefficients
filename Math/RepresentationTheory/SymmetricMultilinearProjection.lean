import Math.RepresentationTheory.SymmetricPowerDescent
import Mathlib.Tactic

/-! Exact finite symmetrization used in species-support projection. -/
namespace Math.SymmetricMultilinearProjection
set_option autoImplicit false
noncomputable section
variable {B N : Type*} [AddCommGroup B] [Module ℂ B]
  [AddCommGroup N] [Module ℂ N] (m : ℕ)

def raw : MultilinearMap ℂ (fun _ : Fin m => B) N →ₗ[ℂ]
    MultilinearMap ℂ (fun _ : Fin m => B) N :=
  (Nat.factorial m : ℂ)⁻¹ • ∑ p : Equiv.Perm (Fin m),
    (MultilinearMap.domDomCongrLinearEquiv ℂ ℂ B N p :
      MultilinearMap ℂ (fun _ : Fin m => B) N ≃ₗ[ℂ] _).toLinearMap

theorem raw_apply (f : MultilinearMap ℂ (fun _ : Fin m => B) N) (w : Fin m → B) :
    raw m f w = (Nat.factorial m : ℂ)⁻¹ • ∑ p : Equiv.Perm (Fin m), f (w ∘ p) := by
  simp only [raw, LinearMap.smul_apply, LinearMap.sum_apply, smul_apply, sum_apply]
  rfl

theorem symmetric (f : MultilinearMap ℂ (fun _ : Fin m => B) N) :
    raw m f ∈ SymmetricPowerDescent.symmetricMaps m := by
  intro q w
  rw [raw_apply, raw_apply]
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft q) _ _ (by intro p; rfl)

def project : MultilinearMap ℂ (fun _ : Fin m => B) N →ₗ[ℂ]
    SymmetricPowerDescent.symmetricMaps (A := B) (N := N) m :=
  (raw m).codRestrict _ (symmetric m)

theorem project_fixed (f : SymmetricPowerDescent.symmetricMaps (A := B) (N := N) m) :
    project m f.val = f := by
  apply Subtype.ext
  ext w
  change raw m f.val w = f.val w
  rw [raw_apply]
  have he : (∑ p : Equiv.Perm (Fin m), f.val (w ∘ p)) =
      ∑ _p : Equiv.Perm (Fin m), f.val w := Finset.sum_congr rfl (fun p _ => f.property p w)
  rw [he]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_smul]

end
end Math.SymmetricMultilinearProjection
