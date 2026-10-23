import Math.RepresentationTheory.Symmetric.SymmetricTensorTrace

/-! A pure-power identity proves factorization through a trace on the entire
symmetric source. This converts local diagram factors into actual kernel
vanishing, without identifying flag evaluation with source completeness. -/
namespace Math.SymmetricTraceFactor
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V N : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup N] [Module ℂ N] (rho : Representation ℂ G V)

theorem factor (p q : ℕ)
    (F : SymmetricTensorTrace.Raw (V := V) (1+p) (1+q) →ₗ[ℂ] N)
    (H : SymmetricTensorTrace.Raw (V := V) p q →ₗ[ℂ] N)
    (h : ∀ v f, F (PiTensorProduct.tprod ℂ (fun _ : Fin (1+p) => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin (1+q) => f)) =
      f v • H (PiTensorProduct.tprod ℂ (fun _ : Fin p => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin q => f))) :
    F.comp (SymmetricTensorTrace.inclusion rho (1+p) (1+q)) =
      (H.comp (SymmetricTensorTrace.rawTrace p q)).comp
        (SymmetricTensorTrace.inclusion rho (1+p) (1+q)) := by
  apply SymmetricPurePowers.tensor_ext
  intro v f
  simp only [LinearMap.comp_apply,SymmetricTensorTrace.inclusion,
    TensorProduct.map_tmul,IntertwiningMap.toLinearMap_apply,
    SymmetricTensorSplit.section_pure_power,SymmetricTensorTrace.rawTrace_pure,map_smul]
  exact h v f

theorem zero_on_kernel (p q : ℕ)
    (F : SymmetricTensorTrace.Raw (V := V) (1+p) (1+q) →ₗ[ℂ] N)
    (H : SymmetricTensorTrace.Raw (V := V) p q →ₗ[ℂ] N)
    (h : ∀ v f, F (PiTensorProduct.tprod ℂ (fun _ : Fin (1+p) => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin (1+q) => f)) =
      f v • H (PiTensorProduct.tprod ℂ (fun _ : Fin p => v) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin q => f)))
    (x : SymmetricTensorTrace.Symmetric (V := V) (1+p) (1+q))
    (hx : SymmetricTensorTrace.trace rho p q x = 0) :
    F (SymmetricTensorTrace.inclusion rho (1+p) (1+q) x) = 0 := by
  have he := LinearMap.congr_fun (factor rho p q F H h) x
  change F (SymmetricTensorTrace.inclusion rho (1+p) (1+q) x) =
    H (SymmetricTensorTrace.rawTrace p q
      (SymmetricTensorTrace.inclusion rho (1+p) (1+q) x)) at he
  rw [(SymmetricTensorTrace.rawTrace_zero_iff rho p q x).mpr hx,map_zero] at he
  exact he

end
end Math.SymmetricTraceFactor
