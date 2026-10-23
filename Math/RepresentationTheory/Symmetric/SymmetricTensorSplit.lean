import Math.RepresentationTheory.Symmetric.SymmetricPowerOperations
import Math.RepresentationTheory.Tensors.TensorPowerDualEquivalence
import Math.LinearAlgebra.Symmetric.SymmetricPurePowers
import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic

/-! Actual symmetric powers are equivariant retracts of tensor powers.
Normalized symmetrization sends a pure power to its pure tensor, uniformly
in the degree, and its image is fixed by every slot permutation. -/
namespace Math.SymmetricTensorSplit
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  (rho : Representation ℂ G V)

@[reducible] local instance (n : ℕ) : AddCommGroup (⨂[ℂ]^n V) := inferInstance
@[reducible] local instance (n : ℕ) : AddCommGroup (Sym[ℂ]^n V) :=
  Module.addCommMonoidToAddCommGroup ℂ

def projection (n : ℕ) : IntertwiningMap (rho.tensorPower n) (rho.symmetricPower n) where
  toLinearMap := SymmetricPower.mk ℂ (Fin n) V
  isIntertwining' g := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    change SymmetricPower.mk ℂ (Fin n) V
        ((rho.tensorPower n) g (PiTensorProduct.tprod ℂ v)) =
      (rho.symmetricPower n) g (SymmetricPower.tprod ℂ v)
    simp only [Representation.tensorPower_apply,PiTensorProduct.map_tprod,
      Representation.symmetricPower_apply_tprod]
    rfl

def sectionMap (n : ℕ) : IntertwiningMap (rho.symmetricPower n) (rho.tensorPower n) where
  toLinearMap := (n.factorial : ℂ)⁻¹ • SymmetricPower.toTensorPower ℂ (Fin n) V
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    change (n.factorial : ℂ)⁻¹ • SymmetricPower.toTensorPower ℂ (Fin n) V
        ((rho.symmetricPower n) g x) =
      (rho.tensorPower n) g ((n.factorial : ℂ)⁻¹ • SymmetricPower.toTensorPower ℂ (Fin n) V x)
    rw [map_smul]
    congr 1
    exact LinearMap.congr_fun (SymmetricPower.toTensorPower_comp_map (rho g)) x

theorem retraction (n : ℕ) (x : Sym[ℂ]^n V) : projection rho n (sectionMap rho n x) = x := by
  change SymmetricPower.mk ℂ (Fin n) V
    ((n.factorial : ℂ)⁻¹ • SymmetricPower.toTensorPower ℂ (Fin n) V x) = x
  rw [map_smul]
  have he := LinearMap.congr_fun
    (SymmetricPower.mk_comp_toTensorPower (R := ℂ) (ι := Fin n) (M := V)) x
  simp only [Fintype.card_fin,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply] at he
  change SymmetricPower.mk ℂ (Fin n) V (SymmetricPower.toTensorPower ℂ (Fin n) V x) =
    n.factorial • x at he
  rw [he,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),one_smul]

def split (n : ℕ) : SplitRepresentationProjection.Split (rho.tensorPower n) (rho.symmetricPower n) where
  project := projection rho n
  embed := sectionMap rho n
  left_inv := retraction rho n

theorem section_pure_power (n : ℕ) (v : V) :
    sectionMap rho n (SymmetricPower.tprod ℂ (fun _ : Fin n => v)) =
      PiTensorProduct.tprod ℂ (fun _ : Fin n => v) := by
  change (n.factorial : ℂ)⁻¹ • SymmetricPower.toTensorPower ℂ (Fin n) V
    (SymmetricPower.tprod ℂ (fun _ : Fin n => v)) = _
  rw [SymmetricPower.toTensorPower_tprod]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ hn,one_smul]

theorem section_permutation (n : ℕ) (sigma : Equiv.Perm (Fin n)) (x : Sym[ℂ]^n V) :
    PiTensorProduct.reindexRepresentation ℂ V (Fin n) sigma (sectionMap rho n x) =
      sectionMap rho n x := by
  suffices he : (PiTensorProduct.reindexRepresentation ℂ V (Fin n) sigma) ∘ₗ
      (sectionMap rho n).toLinearMap = (sectionMap rho n).toLinearMap from
    LinearMap.congr_fun he x
  apply SymmetricPurePowers.ext
  intro v
  change PiTensorProduct.reindexRepresentation ℂ V (Fin n) sigma
    (sectionMap rho n (SymmetricPower.tprod ℂ (fun _ : Fin n => v))) =
      sectionMap rho n (SymmetricPower.tprod ℂ (fun _ : Fin n => v))
  rw [section_pure_power]
  simp only [PiTensorProduct.reindexRepresentation_apply,LinearEquiv.coe_coe,
    PiTensorProduct.reindex_tprod]

end
end Math.SymmetricTensorSplit
