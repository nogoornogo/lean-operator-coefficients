import Math.RepresentationTheory.DualMixedTensorSwap
import Math.RepresentationTheory.SymmetricTensorTrace

/-! Symmetric image and trace transport under the actual color-dual swap.
The bidual is identified by evaluation, with no color self-duality premise. -/
namespace Math.SymmetricDualTensorSwap
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ

def equivalence (p q : ℕ) : Representation.Equiv
    ((rho.dual.symmetricPower p).tprod (rho.dual.dual.symmetricPower q))
      ((rho.symmetricPower q).tprod (rho.dual.symmetricPower p)) :=
  (Representation.TensorProduct.comm _ _).trans
    (tensorEquiv ((bidualEquiv rho).symm.symmetricPower q)
      (.refl (rho.dual.symmetricPower p)))

theorem tprod (p q : ℕ) (v : V) (f : Module.Dual ℂ V) :
    equivalence rho p q
      (SymmetricPower.tprod ℂ (fun _ : Fin p => f) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin q => Module.Dual.eval ℂ V v)) =
      SymmetricPower.tprod ℂ (fun _ : Fin q => v) ⊗ₜ[ℂ]
        SymmetricPower.tprod ℂ (fun _ : Fin p => f) := by
  change ((bidualEquiv rho).symm.symmetricPower q)
    (SymmetricPower.tprod ℂ (fun _ : Fin q => Module.Dual.eval ℂ V v)) ⊗ₜ[ℂ] _ = _
  rw [Representation.Equiv.symmetricPower_apply_tprod]
  congr 1
  congr 1
  funext i
  exact (bidualEquiv rho).toLinearEquiv.symm_apply_apply v

theorem inclusion (p q : ℕ) :
    (SymmetricTensorTrace.inclusion rho q p).comp (equivalence rho p q).toLinearEquiv.toLinearMap =
      (DualMixedTensorSwap.equivalence rho p q).toLinearEquiv.toLinearMap.comp
        (SymmetricTensorTrace.inclusion rho.dual p q) := by
  apply SymmetricPurePowers.tensor_ext
  intro f u
  obtain ⟨v,rfl⟩ := (Module.evalEquiv ℂ V).surjective u
  change SymmetricTensorTrace.inclusion rho q p
    (equivalence rho p q (SymmetricPower.tprod ℂ (fun _ : Fin p => f) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ : Fin q => Module.Dual.eval ℂ V v))) = _
  rw [tprod]
  simp only [SymmetricTensorTrace.inclusion,TensorProduct.map_tmul,
    IntertwiningMap.toLinearMap_apply,SymmetricTensorSplit.section_pure_power,
    LinearMap.comp_apply]
  change (PiTensorProduct.tprod ℂ (fun _ : Fin q => v) ⊗ₜ[ℂ]
    PiTensorProduct.tprod ℂ (fun _ : Fin p => f)) =
      DualMixedTensorSwap.equivalence rho p q
        (PiTensorProduct.tprod ℂ (fun _ : Fin p => f) ⊗ₜ[ℂ]
          PiTensorProduct.tprod ℂ (fun _ : Fin q => Module.Dual.eval ℂ V v))
  exact (DualMixedTensorSwap.tprod rho p q (fun _ => v) (fun _ => f)).symm

theorem trace (p q : ℕ) :
    (SymmetricTensorTrace.rawTrace q p).comp
      ((DualMixedTensorSwap.equivalence rho (1+p) (1+q)).toLinearEquiv.toLinearMap.comp
        (SymmetricTensorTrace.inclusion rho.dual (1+p) (1+q))) =
      (DualMixedTensorSwap.equivalence rho p q).toLinearEquiv.toLinearMap.comp
        ((SymmetricTensorTrace.rawTrace p q).comp
          (SymmetricTensorTrace.inclusion rho.dual (1+p) (1+q))) := by
  apply SymmetricPurePowers.tensor_ext
  intro f u
  obtain ⟨v,rfl⟩ := (Module.evalEquiv ℂ V).surjective u
  simp only [LinearMap.comp_apply,SymmetricTensorTrace.inclusion,TensorProduct.map_tmul,
    IntertwiningMap.toLinearMap_apply,SymmetricTensorSplit.section_pure_power,
    SymmetricTensorTrace.rawTrace_pure,map_smul]
  change SymmetricTensorTrace.rawTrace q p
    (DualMixedTensorSwap.equivalence rho (1+p) (1+q)
      (PiTensorProduct.tprod ℂ (fun _ : Fin (1+p) => f) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin (1+q) => Module.Dual.eval ℂ V v))) =
    f v • DualMixedTensorSwap.equivalence rho p q
      (PiTensorProduct.tprod ℂ (fun _ : Fin p => f) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun _ : Fin q => Module.Dual.eval ℂ V v))
  rw [DualMixedTensorSwap.tprod,SymmetricTensorTrace.rawTrace_pure,DualMixedTensorSwap.tprod]

end
end Math.SymmetricDualTensorSwap
