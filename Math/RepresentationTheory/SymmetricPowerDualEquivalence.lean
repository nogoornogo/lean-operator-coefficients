import Math.RepresentationTheory.SymmetricTensorSplit
import Math.RepresentationTheory.SymmetricDualPairing

/-! Perfect symmetric-power duality in arbitrary finite dimension, with
no irreducibility premise. Normalized tensor sections prove injectivity;
the symbolic symmetric-power dimension identity supplies surjectivity. -/
namespace Math.SymmetricPowerDualEquivalence
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (rho : Representation ℂ G V)

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (Sym[ℂ]^n A) := Module.addCommMonoidToAddCommGroup ℂ
@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance

omit [FiniteDimensional ℂ V] in
theorem pairing_pure_power (n : ℕ) (f : Module.Dual ℂ V) (v : Fin n → V) :
    SymmetricDualPairing.pairing n (SymmetricPower.tprod ℂ (fun _ : Fin n => f))
      (SymmetricPower.tprod ℂ v) = ∏ i, f (v i) := by
  rw [SymmetricDualPairing.pairing_apply]
  have hp (q : Equiv.Perm (Fin n)) : (∏ i, f (v (q i))) = ∏ i, f (v i) :=
    Equiv.prod_comp q (fun i => f (v i))
  simp only [hp,Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_eq_mul]
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

def toDual (n : ℕ) : IntertwiningMap (rho.dual.symmetricPower n) (rho.symmetricPower n).dual where
  toLinearMap := SymmetricDualPairing.pairing n
  isIntertwining' g := by
    apply SymmetricPower.ext
    intro f
    apply SymmetricPower.ext
    intro v
    change SymmetricDualPairing.pairing n
        ((rho.dual.symmetricPower n) g (SymmetricPower.tprod ℂ f)) (SymmetricPower.tprod ℂ v) =
      SymmetricDualPairing.pairing n (SymmetricPower.tprod ℂ f)
        ((rho.symmetricPower n) g⁻¹ (SymmetricPower.tprod ℂ v))
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod,
      SymmetricDualPairing.pairing_apply,SymmetricDualPairing.pairing_apply]
    rfl

theorem tensor_identity (n : ℕ) :
    (TensorPowerDualEquivalence.equivalence rho n).toLinearEquiv.toLinearMap.comp
        (SymmetricTensorSplit.sectionMap rho.dual n).toLinearMap =
      (SymmetricTensorSplit.projection rho n).toLinearMap.dualMap.comp (toDual rho n).toLinearMap := by
  apply SymmetricPurePowers.ext
  intro f
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change TensorPowerDualEquivalence.equivalence rho n
      (SymmetricTensorSplit.sectionMap rho.dual n (SymmetricPower.tprod ℂ (fun _ : Fin n => f)))
        (PiTensorProduct.tprod ℂ v) =
    SymmetricDualPairing.pairing n (SymmetricPower.tprod ℂ (fun _ : Fin n => f))
      (SymmetricPower.tprod ℂ v)
  rw [SymmetricTensorSplit.section_pure_power,
    TensorPowerDualEquivalence.equivalence_tprod,pairing_pure_power]

theorem injective (n : ℕ) : Function.Injective (toDual rho n) := by
  intro x y hxy
  have hx := LinearMap.congr_fun (tensor_identity rho n) x
  have hy := LinearMap.congr_fun (tensor_identity rho n) y
  have he : SymmetricTensorSplit.sectionMap rho.dual n x =
      SymmetricTensorSplit.sectionMap rho.dual n y := by
    apply (TensorPowerDualEquivalence.equivalence rho n).injective
    exact hx.trans ((congrArg (fun f => (SymmetricTensorSplit.projection rho n).toLinearMap.dualMap f)
      hxy).trans hy.symm)
  have hp := congrArg (SymmetricTensorSplit.projection rho.dual n) he
  simpa only [SymmetricTensorSplit.retraction] using hp

theorem dimensions (n : ℕ) : Module.finrank ℂ (Sym[ℂ]^n (Module.Dual ℂ V)) =
    Module.finrank ℂ (Module.Dual ℂ (Sym[ℂ]^n V)) := by
  rw [Subspace.dual_finrank_eq,SymmetricPower.finrank_eq,SymmetricPower.finrank_eq,
    Subspace.dual_finrank_eq]

def equivalence (n : ℕ) : Representation.Equiv
    (rho.dual.symmetricPower n) (rho.symmetricPower n).dual :=
  (toDual rho n).ofBijective ⟨injective rho n,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (dimensions (V := V) n)).mp (injective rho n)⟩

end
end Math.SymmetricPowerDualEquivalence
