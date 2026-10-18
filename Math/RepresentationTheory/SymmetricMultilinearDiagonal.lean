import Math.RepresentationTheory.SymmetricMultilinearProjection

/-! Diagonal evaluation of symmetrization, without enumerating permutations.
Kept separate from the shared projection module and its numerical consumers. -/
namespace Math.SymmetricMultilinearProjection
set_option autoImplicit false
noncomputable section
variable {B N : Type*} [AddCommGroup B] [Module ℂ B]
  [AddCommGroup N] [Module ℂ N] (m : ℕ)

theorem lift_project_diagonal (f : MultilinearMap ℂ (fun _ : Fin m => B) N) (v : B) :
    SymmetricPowerDescent.lift m (project m f)
      (SymmetricPower.tprod ℂ (fun _ : Fin m => v)) = f (fun _ => v) := by
  rw [SymmetricPowerDescent.lift_tprod]
  change raw m f (fun _ => v) = _
  rw [raw_apply]
  change (Nat.factorial m : ℂ)⁻¹ • (∑ _ : Equiv.Perm (Fin m), f (fun _ => v)) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero m), one_smul]

end
end Math.SymmetricMultilinearProjection
