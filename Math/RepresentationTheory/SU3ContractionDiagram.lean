import Math.RepresentationTheory.SU3VolumeContractions
import Math.RepresentationTheory.TensorVolumeEvaluation
import Math.LinearAlgebra.ColorFlagNonvanishing

/-! Canonical spanning contractions agree with vertex-labelled diagrams.
The positive nonvanishing criterion is proved on actual incident color flags;
arbitrary restricted-source vanishing is a separate subsequent connection. -/
namespace Math.SU3ContractionDiagram
set_option autoImplicit false
noncomputable section
open Representation SL3CompactComparison
open scoped TensorProduct

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

theorem formula (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k)))
    (v : Fin (q+3*k) → Vector) (f : Fin q → Module.Dual ℂ Vector) :
    SU3VolumeContractions.contraction q k sigma
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      (∏ i : Fin q, f i (v (sigma.symm (Fin.castAdd (3*k) i)))) *
        ∏ a : Fin k, SU3VolumeContractions.basis.det
          (fun j => v (sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j)))) := by
  rw [SU3VolumeContractions.contraction_apply]
  simp only [TauCeti.permTensorAction_apply,LinearEquiv.coe_coe,PiTensorProduct.reindex_tprod]
  unfold SU3VolumeContractions.volumeSplit
  rw [TensorVolumeEvaluation.raiseDegree_tprod, map_smul,
    TensorPowerDualEquivalence.equivalence_tprod]
  exact mul_comm _ _

variable {J : Type*}

def pairs (q k : ℕ) (v : Fin (q+3*k) → J) (f : Fin q → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) : Fin q → J × J :=
  fun i => (f i,v (sigma.symm (Fin.castAdd (3*k) i)))

def triples (q k : ℕ) (v : Fin (q+3*k) → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) : Fin k → Fin 3 → J :=
  fun a j => v (sigma.symm (Fin.natAdd q (TensorVolumeEvaluation.blockIndex 3 k a j)))

theorem basis_det (v : J → Vector) (i : Fin 3 → J) :
    SU3VolumeContractions.basis.det (fun j => v (i j)) =
      ColorFlagNonvanishing.determinant v i := by
  rw [Module.Basis.det_apply]
  rfl

theorem flag_formula (q k : ℕ) (v : Fin (q+3*k) → J) (f : Fin q → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) (a : J × Fin 3 → ℂ) :
    SU3VolumeContractions.contraction q k sigma
      (PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.vector a (v i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.functional a (f i))) =
      ColorFlagNonvanishing.value a (pairs q k v f sigma) (triples q k v sigma)
        (fun i : Fin 0 => Fin.elim0 i) := by
  rw [formula]
  simp only [ColorFlagNonvanishing.functional_apply,basis_det,
    ColorFlagNonvanishing.value,Fin.prod_univ_zero,mul_one,pairs,
    ColorFlagNonvanishing.pair]
  rfl

/-- This finite permutation predicate is the positive diagram test, with
no unevaluated Hom, kernel or multiplicity on its right side. -/
theorem flag_nonzero_iff (q k : ℕ) (v : Fin (q+3*k) → J) (f : Fin q → J)
    (sigma : Equiv.Perm (Fin (q+3*k))) :
    (∃ a : J × Fin 3 → ℂ, SU3VolumeContractions.contraction q k sigma
      (PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.vector a (v i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => ColorFlagNonvanishing.functional a (f i))) ≠ 0) ↔
      (∀ i : Fin q, f i ≠ v (sigma.symm (Fin.castAdd (3*k) i))) ∧
        (∀ a : Fin k, Function.Injective (triples q k v sigma a)) := by
  simp only [flag_formula]
  have he := ColorFlagNonvanishing.nonzero_iff
    (pairs q k v f sigma) (triples q k v sigma) (fun i : Fin 0 => Fin.elim0 i)
  simpa only [pairs,Fin.forall_fin_zero,forall_const,and_true] using he

end
end Math.SU3ContractionDiagram
