import Math.RepresentationTheory.Color.SU3.SL3TensorCommutant
import Math.RepresentationTheory.Tensors.TensorPowerDualEquivalence

/-! Every balanced compact-color tensor coefficient is a finite linear
combination of evaluation contractions. No coefficient or rank table is used. -/
namespace Math.SU3BalancedContractions
set_option autoImplicit false
noncomputable section
open Representation SL3ColorPlanes SL3CompactComparison
open scoped TensorProduct

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance
@[reducible] local instance (a b : ℕ) : AddCommGroup (MixedCarrier a b) := inferInstance

def extend (a b : ℕ)
    (f : InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed a b)) :
    InvariantCoefficientTransport.Invariants (mixed a b) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    exact mixed_invariant a b f.toLinearMap (fun u y => f.isIntertwining _ _ u y) g x

def endomorphism (n : ℕ)
    (f : InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed n n)) :
    IntertwiningMap (standard.tensorPower n) (standard.tensorPower n) :=
  TensorPowerDualEquivalence.curry standard n n (extend n n f)

theorem permutation_image (n : ℕ)
    (f : InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed n n)) :
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)),
      TauCeti.permTensorActionAlgHom ℂ 3 n a = (endomorphism n f).toLinearMap :=
  SL3TensorCommutant.permutation_image n _ (fun g => (endomorphism n f).isIntertwining' g)

/-- The formula keeps all degree and permutation indices symbolic. -/
theorem formula (n : ℕ)
    (f : InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed n n)) :
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin n)),
      ∀ (v : Fin n → Vector) (phi : Fin n → Module.Dual ℂ Vector),
        f (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ phi) =
          a.coeff.sum (fun sigma c => c * ∏ i, phi i (v (sigma.symm i))) := by
  obtain ⟨a,ha⟩ := permutation_image n f
  refine ⟨a,?_⟩
  intro v phi
  have he := TensorPowerDualEquivalence.curry_apply standard n n (extend n n f)
    (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ phi)
  change TensorPowerDualEquivalence.equivalence standard n (PiTensorProduct.tprod ℂ phi)
    (endomorphism n f (PiTensorProduct.tprod ℂ v)) =
      f (PiTensorProduct.tprod ℂ v ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ phi) at he
  rw [← he]
  change TensorPowerDualEquivalence.equivalence standard n (PiTensorProduct.tprod ℂ phi)
    ((endomorphism n f).toLinearMap (PiTensorProduct.tprod ℂ v)) = _
  rw [← ha,TauCeti.permTensorActionAlgHom_apply_tprod]
  simp only [Finsupp.sum,map_sum,map_smul,
    TensorPowerDualEquivalence.equivalence_tprod,smul_eq_mul]

end
end Math.SU3BalancedContractions
