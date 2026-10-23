import Math.RepresentationTheory.Symmetric.SymmetricTensorTrace

/-! Insert a fixed vector in an arbitrary tensor slot, retaining a symbolic
degree. On a pure power this is precisely a one-slot function update. -/
namespace Math.TensorSlotInsertion
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def insert (p : ℕ) (j : Fin (1+p)) (e : V) : (⨂[ℂ]^p V) →ₗ[ℂ] (⨂[ℂ]^(1+p) V) :=
  (PiTensorProduct.reindexRepresentation ℂ V (Fin (1+p))
    (Equiv.swap (Fin.castAdd p 0) j)).comp
      ((SymmetricTensorTrace.first p).symm.toLinearMap.comp (TensorProduct.mk ℂ _ _ e))

theorem first_symm (p : ℕ) (e v : V) :
    (SymmetricTensorTrace.first p).symm
      (e ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun _ : Fin p => v)) =
      PiTensorProduct.tprod ℂ (Function.update (fun _ : Fin (1+p) => v) (Fin.castAdd p 0) e) := by
  classical
  apply (SymmetricTensorTrace.first p).injective
  rw [LinearEquiv.apply_symm_apply,SymmetricTensorTrace.first_tprod,Function.update_self]
  congr 1
  congr 1
  funext i
  have hi : Fin.natAdd 1 i ≠ Fin.castAdd p (0 : Fin 1) := by
    intro h
    have hv := congrArg (fun z : Fin (1+p) => z.val) h
    change 1+i.val = 0 at hv
    omega
  exact (Function.update_of_ne hi e (fun _ : Fin (1+p) => v)).symm

theorem pure (p : ℕ) (j : Fin (1+p)) (e v : V) :
    insert p j e (PiTensorProduct.tprod ℂ (fun _ : Fin p => v)) =
      PiTensorProduct.tprod ℂ (Function.update (fun _ : Fin (1+p) => v) j e) := by
  classical
  simp only [insert,LinearMap.comp_apply,TensorProduct.mk_apply,first_symm,
    PiTensorProduct.reindexRepresentation_apply,LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod,Equiv.symm_swap]
  congr 1
  funext i
  by_cases hi : i = j
  · subst i
    simp
  · have hn : Equiv.swap (Fin.castAdd p 0) j i ≠ Fin.castAdd p 0 := by
      intro he
      have := congrArg (Equiv.swap (Fin.castAdd p 0) j) he
      rw [Equiv.swap_apply_self,Equiv.swap_apply_left] at this
      exact hi this
    simp only [Function.update_of_ne hi,Function.update_of_ne hn]

end
end Math.TensorSlotInsertion
