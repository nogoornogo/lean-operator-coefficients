import Math.RepresentationTheory.Tensors.InvolutionYoung

/-! The first two Young shapes, (2) and (1,1), for tensor-slot exchange. -/
namespace Math.TwoSlotYoung
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct
variable {H F : Type*} [Group H] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ H F)

abbrev swap := (Representation.TensorProduct.comm a a).toIntertwiningMap

theorem swap_involutive (w : F ⊗[ℂ] F) : swap a (swap a w) = w := by
  exact (Representation.TensorProduct.comm a a).toLinearEquiv.symm_apply_apply w

abbrev symmetric := InvolutionYoung.eigenRepresentation (a.tprod a) (swap a) 1
abbrev antisymmetric := InvolutionYoung.eigenRepresentation (a.tprod a) (swap a) (-1)

def splitting : Representation.Equiv (a.tprod a) ((symmetric a).prod (antisymmetric a)) :=
  InvolutionYoung.splitting (a.tprod a) (swap a) (swap_involutive a)

def symmetricQuotientEquiv :=
  InvolutionYoung.quotientEquiv (a.tprod a) (swap a) (swap_involutive a) 1 (by norm_num)

def antisymmetricQuotientEquiv :=
  InvolutionYoung.quotientEquiv (a.tprod a) (swap a) (swap_involutive a) (-1) (by norm_num)

theorem symmetric_projector (u v : F) :
    InvolutionYoung.projector (a.tprod a) (swap a) 1 (u ⊗ₜ[ℂ] v) =
      (1 / 2 : ℂ) • (u ⊗ₜ[ℂ] v + v ⊗ₜ[ℂ] u) := by
  simp [InvolutionYoung.projector_apply, swap]

theorem antisymmetric_projector (u v : F) :
    InvolutionYoung.projector (a.tprod a) (swap a) (-1) (u ⊗ₜ[ℂ] v) =
      (1 / 2 : ℂ) • (u ⊗ₜ[ℂ] v - v ⊗ₜ[ℂ] u) := by
  simp [InvolutionYoung.projector_apply, swap, sub_eq_add_neg]

theorem antisymmetric_diagonal (u : F) :
    InvolutionYoung.projector (a.tprod a) (swap a) (-1) (u ⊗ₜ[ℂ] u) = 0 := by
  rw [antisymmetric_projector, sub_self, smul_zero]

end
end Math.TwoSlotYoung
