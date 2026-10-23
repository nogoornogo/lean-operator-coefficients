import Math.RepresentationTheory.Symmetric.SymmetricMultilinearProjection
import Math.RepresentationTheory.Tensors.InvariantTensorCurry
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RepresentationTheory.Irreducible
import TauCeti.LinearAlgebra.SymmetricPower.Basis

/-! Actual symmetric-power evaluation pairing, without identifying an ordered
tensor pairing with a descended coefficient. -/
namespace Math.SymmetricDualPairing
set_option autoImplicit false
noncomputable section
open Representation
open scoped TensorProduct BigOperators
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def inner (m : ℕ) : MultilinearMap ℂ (fun _ : Fin m => Module.Dual ℂ V)
    (Sym[ℂ]^m V →ₗ[ℂ] ℂ) :=
  ((SymmetricPowerDescent.equiv m).symm.toLinearMap.comp
    (SymmetricMultilinearProjection.project m)).compMultilinearMap
      (MultilinearMap.piLinearMap (MultilinearMap.mkPiAlgebra ℂ (Fin m) ℂ))

def pairing (m : ℕ) : Sym[ℂ]^m (Module.Dual ℂ V) →ₗ[ℂ] Module.Dual ℂ (Sym[ℂ]^m V) :=
  SymmetricPowerDescent.lift m (SymmetricMultilinearProjection.project m (inner m))

theorem pairing_apply (m : ℕ) (φ : Fin m → Module.Dual ℂ V) (v : Fin m → V) :
    pairing m (SymmetricPower.tprod ℂ φ) (SymmetricPower.tprod ℂ v) =
      (m.factorial : ℂ)⁻¹ * ∑ p : Equiv.Perm (Fin m),
        (m.factorial : ℂ)⁻¹ * ∑ q : Equiv.Perm (Fin m), ∏ i, φ (p i) (v (q i)) := by
  simp [pairing,inner,SymmetricPowerDescent.equiv,SymmetricPowerDescent.lift_tprod,
    SymmetricMultilinearProjection.project,SymmetricMultilinearProjection.raw_apply,
    MultilinearMap.piLinearMap,MultilinearMap.compLinearMapMultilinear,
    Function.comp_def,smul_eq_mul]

theorem diagonal (m : ℕ) (φ : Module.Dual ℂ V) (v : V) :
    pairing m (SymmetricPower.tprod ℂ (fun _ => φ))
      (SymmetricPower.tprod ℂ (fun _ => v)) = (φ v)^m := by
  rw [pairing_apply]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.sum_const,
    Fintype.card_perm,← Nat.cast_smul_eq_nsmul ℂ,smul_eq_mul]
  have hn : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  field_simp

variable {G : Type*} [Group G] (b : Representation ℂ G V)

theorem pairing_invariant (m : ℕ) (g : G) (φ : Fin m → Module.Dual ℂ V)
    (v : Fin m → V) :
    pairing m (SymmetricPower.tprod ℂ (fun i => b.dual g (φ i)))
      (SymmetricPower.tprod ℂ (fun i => b g (v i))) =
    pairing m (SymmetricPower.tprod ℂ φ) (SymmetricPower.tprod ℂ v) := by
  rw [pairing_apply,pairing_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.prod_congr rfl
  intro i hi
  change φ (p i) (b g⁻¹ (b g (v (q i)))) = φ (p i) (v (q i))
  simp [← Module.End.mul_apply,← map_mul]

def coefficient (m : ℕ) : IntertwiningMap
    ((b.symmetricPower m).tprod (b.dual.symmetricPower m)) (trivial ℂ G ℂ) where
  toLinearMap := TensorProduct.lift (pairing m).flip
  isIntertwining' g := by
    apply TensorProduct.ext
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin m) V)
    rintro _ ⟨v,rfl⟩
    apply LinearMap.ext_on (SymmetricPower.span_tprod_eq_top ℂ (Fin m) (Module.Dual ℂ V))
    rintro _ ⟨φ,rfl⟩
    change pairing m (b.dual.symmetricPower m g (SymmetricPower.tprod ℂ φ))
      (b.symmetricPower m g (SymmetricPower.tprod ℂ v)) =
        pairing m (SymmetricPower.tprod ℂ φ) (SymmetricPower.tprod ℂ v)
    rw [Representation.symmetricPower_apply_tprod,Representation.symmetricPower_apply_tprod]
    exact pairing_invariant b m g φ v

theorem coefficient_diagonal (m : ℕ) (v : V) (φ : Module.Dual ℂ V) :
    coefficient b m (SymmetricPower.tprod ℂ (fun _ => v) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ (fun _ => φ)) = (φ v)^m := diagonal m φ v

def toDual (m : ℕ) : IntertwiningMap (b.symmetricPower m) (b.dual.symmetricPower m).dual :=
  InvariantTensorCurry.curry _ _ (coefficient b m)

theorem toDual_nonzero (m : ℕ) (v : V) (φ : Module.Dual ℂ V) (hv : φ v ≠ 0) :
    toDual b m ≠ 0 := by
  intro hz
  have he := congrArg (fun f : IntertwiningMap (b.symmetricPower m)
    (b.dual.symmetricPower m).dual => f (SymmetricPower.tprod ℂ (fun _ => v))
      (SymmetricPower.tprod ℂ (fun _ => φ))) hz
  exact pow_ne_zero m hv (by simpa [toDual,InvariantTensorCurry.curry,
    coefficient_diagonal] using he)

variable [FiniteDimensional ℂ V]

theorem ranks_equal (m : ℕ) : Module.finrank ℂ (Sym[ℂ]^m V) =
    Module.finrank ℂ (Module.Dual ℂ (Sym[ℂ]^m (Module.Dual ℂ V))) := by
  rw [Subspace.dual_finrank_eq,SymmetricPower.finrank_eq,SymmetricPower.finrank_eq,
    Subspace.dual_finrank_eq]

/-- Irreducibility plus one actual evaluation makes the pairing perfect. -/
def equiv (m : ℕ) [IsIrreducible (b.symmetricPower m)]
    (v : V) (φ : Module.Dual ℂ V) (hv : φ v ≠ 0) :
    Representation.Equiv (b.symmetricPower m) (b.dual.symmetricPower m).dual := by
  have hi := (IsIrreducible.injective_or_eq_zero (toDual b m)).resolve_right
    (toDual_nonzero b m v φ hv)
  exact (toDual b m).ofBijective ⟨hi,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (ranks_equal (V := V) m)).mp hi⟩

end
end Math.SymmetricDualPairing
