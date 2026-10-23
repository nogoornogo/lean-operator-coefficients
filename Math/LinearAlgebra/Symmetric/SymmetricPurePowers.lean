import TauCeti.LinearAlgebra.Multilinear.Polarization
import TauCeti.LinearAlgebra.SymmetricPower.Lift
import Mathlib.Basic.Complex.Basic

/-! Pure powers span complex symmetric powers, by the pinned polarization identity. -/
namespace Math.SymmetricPurePowers
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
variable {V N : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup N] [Module ℂ N]

theorem span (n : ℕ) :
    Submodule.span ℂ (Set.range (fun v : V =>
      SymmetricPower.tprod ℂ (fun _ : Fin n => v))) = ⊤ := by
  classical
  let P := Submodule.span ℂ (Set.range (fun v : V =>
    SymmetricPower.tprod ℂ (fun _ : Fin n => v)))
  apply top_unique
  rw [← SymmetricPower.span_tprod_eq_top ℂ (Fin n) V]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, rfl⟩
  change SymmetricPower.tprod ℂ v ∈ P
  have he := MultilinearMap.sum_neg_one_pow_card_smul_apply_sum_compl
    (SymmetricPower.tprod ℂ (ι := Fin n) (M := V)) v
  have hr : (∑ σ : Equiv.Perm (Fin n),
      SymmetricPower.tprod ℂ (fun i => v (σ i))) =
      (Nat.factorial n : ℂ) • SymmetricPower.tprod ℂ v := by
    simp only [SymmetricPower.tprod_equiv, Finset.sum_const, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin, Nat.cast_smul_eq_nsmul]
  rw [hr] at he
  have hp : (Nat.factorial n : ℂ) • SymmetricPower.tprod ℂ v ∈ P := by
    rw [← he]
    exact P.sum_mem fun s _ => P.smul_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  have hn : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
    P.smul_mem (Nat.factorial n : ℂ)⁻¹ hp

theorem ext {n : ℕ} {f g : Sym[ℂ]^n V →ₗ[ℂ] N}
    (h : ∀ v, f (SymmetricPower.tprod ℂ (fun _ : Fin n => v)) =
      g (SymmetricPower.tprod ℂ (fun _ : Fin n => v))) : f = g := by
  apply LinearMap.ext_on (span (V := V) n)
  rintro _ ⟨v, rfl⟩
  exact h v

theorem tensor_ext {W : Type*} [AddCommGroup W] [Module ℂ W] {n m : ℕ}
    {f g : Sym[ℂ]^n V ⊗[ℂ] Sym[ℂ]^m W →ₗ[ℂ] N}
    (h : ∀ v w, f (SymmetricPower.tprod ℂ (fun _ : Fin n => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin m => w)) =
      g (SymmetricPower.tprod ℂ (fun _ : Fin n => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin m => w))) : f = g := by
  apply TensorProduct.ext'
  intro x y
  have hx : f.comp ((TensorProduct.mk ℂ _ _).flip y) =
      g.comp ((TensorProduct.mk ℂ _ _).flip y) := by
    apply ext
    intro v
    have hy : f.comp (TensorProduct.mk ℂ _ _ (SymmetricPower.tprod ℂ (fun _ : Fin n => v))) =
        g.comp (TensorProduct.mk ℂ _ _ (SymmetricPower.tprod ℂ (fun _ : Fin n => v))) := by
      apply ext
      intro w
      exact h v w
    exact LinearMap.congr_fun hy y
  exact LinearMap.congr_fun hx x

end
end Math.SymmetricPurePowers
