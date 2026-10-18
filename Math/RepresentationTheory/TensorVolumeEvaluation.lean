import Math.RepresentationTheory.TensorVolumeSplit
import Math.RepresentationTheory.TensorContractionSpan
import Mathlib.Algebra.BigOperators.Fin

/-! The canonical determinant-block projection on an arbitrary tensor power
evaluates as a product of determinants. All block indices remain symbolic. -/
namespace Math.TensorVolumeEvaluation
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  {n : ℕ} (rho : Representation ℂ G V) (b : Module.Basis (Fin n) ℂ V)
  (hd : ∀ g, LinearMap.det (rho g) = 1)

@[reducible] local instance (p : ℕ) : AddCommGroup (⨂[ℂ]^p V) := inferInstance

def blockIndex (n k : ℕ) (a : Fin k) (i : Fin n) : Fin (n*k) :=
  ⟨a.val*n+i.val,by
    calc
      a.val*n+i.val < a.val*n+n := Nat.add_lt_add_left i.isLt _
      _ = (a.val+1)*n := by rw [Nat.add_mul,Nat.one_mul]
      _ ≤ k*n := Nat.mul_le_mul_right n a.isLt
      _ = n*k := Nat.mul_comm _ _⟩

theorem split_tprod (p q : ℕ) (v : Fin (p+q) → V) :
    (rho.tensorPowerAddEquiv p q).symm (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd q i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd p i)) := by
  apply (rho.tensorPowerAddEquiv p q).injective
  change rho.tensorPowerAddEquiv p q
      ((rho.tensorPowerAddEquiv p q).symm (PiTensorProduct.tprod ℂ v)) =
    rho.tensorPowerAddEquiv p q
      (PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd q i)) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd p i)))
  rw [Representation.Equiv.apply_symm_apply]
  change PiTensorProduct.tprod ℂ v = _root_.TensorPower.mulEquiv
    (PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd q i)) ⊗ₜ[ℂ]
      PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd p i)))
  rw [← _root_.TensorPower.gMul_def,_root_.TensorPower.tprod_mul_tprod]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [Fin.append]

theorem add_project {p q : ℕ}
    (S : SplitRepresentationProjection.Split (rho.tensorPower p) (trivial ℂ G ℂ))
    (T : SplitRepresentationProjection.Split (rho.tensorPower q) (trivial ℂ G ℂ))
    (v : Fin (p+q) → V) :
    (TensorVolumeSplit.add rho S T).project (PiTensorProduct.tprod ℂ v) =
      S.project (PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd q i))) *
        T.project (PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd p i))) := by
  change Representation.TensorProduct.lid ℂ (trivial ℂ G ℂ)
    ((S.project.tensor T.project) ((rho.tensorPowerAddEquiv p q).symm
      (PiTensorProduct.tprod ℂ v))) = _
  rw [split_tprod]
  rfl

theorem multiple_tprod (k : ℕ) (v : Fin (n*k) → V) :
    (TensorVolumeSplit.multiple rho b hd k).project (PiTensorProduct.tprod ℂ v) =
      ∏ a : Fin k, b.det (fun i => v (blockIndex n k a i)) := by
  induction k with
  | zero =>
    simp [TensorVolumeSplit.multiple,TensorVolumeSplit.zeroEquivalence,
      SplitRepresentationProjection.Split.ofEquiv]
  | succ k ih =>
    change (TensorVolumeSplit.add rho (TensorVolumeSplit.multiple rho b hd k)
      (TensorVolumeSplit.split rho b hd)).project
        (TensorVolumeSplit.powerCast rho (Nat.mul_succ n k) (PiTensorProduct.tprod ℂ v)) = _
    rw [TensorVolumeSplit.powerCast_tprod,add_project,ih]
    change (∏ a : Fin k, b.det (fun i =>
        v (Fin.cast (Nat.mul_succ n k).symm (Fin.castAdd n (blockIndex n k a i))))) *
      TensorVolumeSplit.coefficient rho b hd
        (PiTensorProduct.tprod ℂ (fun i =>
          v (Fin.cast (Nat.mul_succ n k).symm (Fin.natAdd (n*k) i)))) = _
    rw [TensorVolumeSplit.coefficient_tprod,Fin.prod_univ_castSucc]
    refine congrArg₂ (·*·) ?_ ?_
    · rfl
    · congr 1
      funext i
      apply congrArg v
      apply Fin.ext
      change n*k+i.val = k*n+i.val
      rw [Nat.mul_comm n k]

theorem raiseDegree_tprod (q k : ℕ) (v : Fin (q+n*k) → V) :
    (TensorVolumeSplit.raiseDegree rho b hd q k).project (PiTensorProduct.tprod ℂ v) =
      (∏ a : Fin k, b.det (fun i => v (Fin.natAdd q (blockIndex n k a i)))) •
        PiTensorProduct.tprod ℂ (fun i : Fin q => v (Fin.castAdd (n*k) i)) := by
  change Representation.TensorProduct.rid ℂ (rho.tensorPower q)
    (((IntertwiningMap.id (rho.tensorPower q)).tensor (TensorVolumeSplit.multiple rho b hd k).project)
      ((rho.tensorPowerAddEquiv q (n*k)).symm (PiTensorProduct.tprod ℂ v))) = _
  rw [split_tprod]
  change (TensorVolumeSplit.multiple rho b hd k).project
      (PiTensorProduct.tprod ℂ (fun i => v (Fin.natAdd q i))) •
        PiTensorProduct.tprod ℂ (fun i => v (Fin.castAdd (n*k) i)) = _
  rw [multiple_tprod]

theorem contraction_tprod [FiniteDimensional ℂ V] (q k : ℕ)
    (sigma : Equiv.Perm (Fin (q+n*k)))
    (v : Fin (q+n*k) → V) (f : Fin q → Module.Dual ℂ V) :
    TensorContractionSpan.contraction rho b hd q k sigma
      (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ f) =
      (∏ i : Fin q, f i (v (sigma.symm (Fin.castAdd (n*k) i)))) *
        ∏ a : Fin k, b.det
          (fun j => v (sigma.symm (Fin.natAdd q (blockIndex n k a j)))) := by
  rw [TensorContractionSpan.contraction_apply]
  simp only [TensorContractionSpan.perm,PiTensorProduct.reindexRepresentation_apply,
    LinearEquiv.coe_coe,PiTensorProduct.reindex_tprod]
  rw [raiseDegree_tprod,map_smul,TensorPowerDualEquivalence.equivalence_tprod]
  exact mul_comm _ _

end
end Math.TensorVolumeEvaluation
