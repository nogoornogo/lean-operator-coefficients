import Math.RepresentationTheory.SU3ContractionDiagram
import Math.RepresentationTheory.SU3MixedContractionSpan

/-! Canonical contraction diagrams for excess covector degree, retaining
the actual contragredient action and bidual transport. -/
namespace Math.SU3DualContractionDiagram
set_option autoImplicit false
noncomputable section
open Representation SL3CompactComparison
open scoped TensorProduct

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

theorem formula (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k)))
    (v : Fin q → Vector) (f : Fin (q+3*k) → Module.Dual ℂ Vector) :
    SU3MixedContractionSpan.dualContraction q k sigma
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      (∏ i : Fin q, f (sigma.symm (Fin.castAdd (3*k) i)) (v i)) *
        ∏ a : Fin k, SU3MixedContractionSpan.dualBasis.det
          (fun j => f (sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j)))) := by
  change TensorContractionSpan.contraction standard.dual SU3MixedContractionSpan.dualBasis
    SU3MixedContractionSpan.dual_determinant q k sigma
      ((SU3MixedContractionSpan.dualSwap (q+3*k) q).symm
        (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f)) = _
  rw [SU3MixedContractionSpan.dualSwap_symm_tprod,TensorVolumeEvaluation.contraction_tprod]
  rfl

variable {J : Type*}

def pairs (q k : ℕ) (v : Fin q → J) (f : Fin (q+3*k) → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) : Fin q → J × J :=
  fun i => (f (sigma.symm (Fin.castAdd (3*k) i)),v i)

def triples (q k : ℕ) (f : Fin (q+3*k) → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) : Fin k → Fin 3 → J :=
  SU3ContractionDiagram.triples q k f sigma

theorem functional_basis (a : J × Fin 3 → ℂ) (i : J) (j : Fin 3) :
    ColorFlagNonvanishing.functional a i (Pi.single j 1) = ColorFlagNonvanishing.covector a i j := by
  classical
  simp [ColorFlagNonvanishing.functional_apply,Pi.single_apply]

theorem basis_det (a : J × Fin 3 → ℂ) (i : Fin 3 → J) :
    SU3MixedContractionSpan.dualBasis.det (fun j => ColorFlagNonvanishing.functional a (i j)) =
      ColorFlagNonvanishing.determinant (ColorFlagNonvanishing.covector a) i := by
  rw [Module.Basis.det_apply]
  apply congrArg Matrix.det
  ext j k
  change (Pi.basisFun ℂ (Fin 3)).dualBasis.repr
    (ColorFlagNonvanishing.functional a (i k)) j = ColorFlagNonvanishing.covector a (i k) j
  rw [Module.Basis.dualBasis_repr]
  simpa only [Pi.basisFun_apply] using functional_basis a (i k) j

theorem flag_formula (q k : ℕ) (v : Fin q → J) (f : Fin (q+3*k) → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) (a : J × Fin 3 → ℂ) :
    SU3MixedContractionSpan.dualContraction q k sigma
      (PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.vector a (v i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.functional a (f i))) =
      ColorFlagNonvanishing.value a (pairs q k v f sigma)
        (fun i : Fin 0 => Fin.elim0 i) (triples q k f sigma) := by
  rw [formula]
  simp only [ColorFlagNonvanishing.functional_apply,basis_det,
    ColorFlagNonvanishing.value,Fin.prod_univ_zero,mul_one,pairs,
    ColorFlagNonvanishing.pair]
  rfl

theorem flag_nonzero_iff (q k : ℕ) (v : Fin q → J) (f : Fin (q+3*k) → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) :
    (∃ a : J × Fin 3 → ℂ, SU3MixedContractionSpan.dualContraction q k sigma
      (PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.vector a (v i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.functional a (f i))) ≠ 0) ↔
      (∀ i : Fin q, f (sigma.symm (Fin.castAdd (3*k) i)) ≠ v i) ∧
        (∀ a : Fin k, Function.Injective (triples q k f sigma a)) := by
  simp only [flag_formula]
  have he := ColorFlagNonvanishing.nonzero_iff
    (pairs q k v f sigma) (fun i : Fin 0 => Fin.elim0 i) (triples q k f sigma)
  simpa only [pairs,Fin.forall_fin_zero,forall_const,true_and] using he

end
end Math.SU3DualContractionDiagram
