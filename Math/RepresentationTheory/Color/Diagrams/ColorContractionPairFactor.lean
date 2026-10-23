import Math.RepresentationTheory.Color.SU3.SU3ContractionDiagram
import Math.RepresentationTheory.Color.SU3.SU3DualContractionDiagram

/-! Every raw slot is used exactly once in a canonical contraction. Replacing
one evaluation pair by a normalized fixed pair extracts its scalar factor. -/
namespace Math.ColorContractionPairFactor
set_option autoImplicit false
noncomputable section
open Representation SU3DefiningExterior
open scoped TensorProduct

theorem selected_ne (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k)))
    {i j : Fin q} (h : j ≠ i) :
    sigma.symm (Fin.castAdd (3*k) j) ≠ sigma.symm (Fin.castAdd (3*k) i) := by
  intro he
  apply h
  apply Fin.ext
  exact congrArg (fun z : Fin (q+3*k) => z.val) (sigma.symm.injective he)

theorem volume_ne (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k)))
    (i : Fin q) (a : Fin k) (j : Fin 3) :
    sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j)) ≠
      sigma.symm (Fin.castAdd (3*k) i) := by
  intro he
  have hv := congrArg Fin.val (sigma.symm.injective he)
  change q + _ = i.val at hv
  have hi := i.isLt
  omega

theorem positive (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k))) (i : Fin q)
    (v : Fin (q+3*k) → Vector) (f : Fin q → Module.Dual ℂ Vector)
    (e : Vector) (epsilon : Module.Dual ℂ Vector) (he : epsilon e = 1) :
    SU3VolumeContractions.contraction q k sigma
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      f i (v (sigma.symm (Fin.castAdd (3*k) i))) *
        SU3VolumeContractions.contraction q k sigma
          (PiTensorProduct.tprod ℂ (Function.update v (sigma.symm (Fin.castAdd (3*k) i)) e) ⊗ₜ[ℂ]
            PiTensorProduct.tprod ℂ (Function.update f i epsilon)) := by
  classical
  rw [SU3ContractionDiagram.formula,SU3ContractionDiagram.formula]
  have hv : (∏ a : Fin k, SU3VolumeContractions.basis.det (fun j =>
        Function.update v (sigma.symm (Fin.castAdd (3*k) i)) e
          (sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j))))) =
      ∏ a : Fin k, SU3VolumeContractions.basis.det (fun j =>
        v (sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j)))) := by
    apply Finset.prod_congr rfl
    intro a _
    congr 1
    funext j
    exact Function.update_of_ne (volume_ne q k sigma i a j) _ _
  rw [hv]
  have hp : (∏ j : Fin q, Function.update f i epsilon j
        (Function.update v (sigma.symm (Fin.castAdd (3*k) i)) e
          (sigma.symm (Fin.castAdd (3*k) j)))) =
      ∏ j ∈ Finset.univ.erase i, f j (v (sigma.symm (Fin.castAdd (3*k) j))) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self,he,one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    rw [Function.update_of_ne hji,Function.update_of_ne (selected_ne q k sigma hji)]
  rw [hp,← mul_assoc]
  congr 1
  exact (Finset.mul_prod_erase Finset.univ
    (fun j => f j (v (sigma.symm (Fin.castAdd (3*k) j)))) (Finset.mem_univ i)).symm

theorem negative (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k))) (i : Fin q)
    (v : Fin q → Vector) (f : Fin (q+3*k) → Module.Dual ℂ Vector)
    (e : Vector) (epsilon : Module.Dual ℂ Vector) (he : epsilon e = 1) :
    SU3MixedContractionSpan.dualContraction q k sigma
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      f (sigma.symm (Fin.castAdd (3*k) i)) (v i) *
        SU3MixedContractionSpan.dualContraction q k sigma
          (PiTensorProduct.tprod ℂ (Function.update v i e) ⊗ₜ[ℂ]
            PiTensorProduct.tprod ℂ (Function.update f (sigma.symm (Fin.castAdd (3*k) i)) epsilon)) := by
  classical
  rw [SU3DualContractionDiagram.formula,SU3DualContractionDiagram.formula]
  have hv : (∏ a : Fin k, SU3MixedContractionSpan.dualBasis.det (fun j =>
        Function.update f (sigma.symm (Fin.castAdd (3*k) i)) epsilon
          (sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j))))) =
      ∏ a : Fin k, SU3MixedContractionSpan.dualBasis.det (fun j =>
        f (sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j)))) := by
    apply Finset.prod_congr rfl
    intro a _
    congr 1
    funext j
    exact Function.update_of_ne (volume_ne q k sigma i a j) _ _
  rw [hv]
  have hp : (∏ j : Fin q, Function.update f (sigma.symm (Fin.castAdd (3*k) i)) epsilon
        (sigma.symm (Fin.castAdd (3*k) j)) (Function.update v i e j)) =
      ∏ j ∈ Finset.univ.erase i, f (sigma.symm (Fin.castAdd (3*k) j)) (v j) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self,he,one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    rw [Function.update_of_ne hji,Function.update_of_ne (selected_ne q k sigma hji)]
  rw [hp,← mul_assoc]
  congr 1
  exact (Finset.mul_prod_erase Finset.univ
    (fun j => f (sigma.symm (Fin.castAdd (3*k) j)) (v j)) (Finset.mem_univ i)).symm

end
end Math.ColorContractionPairFactor
