import Math.RepresentationTheory.Color.SU3.SU3BalancedContractions
import Math.RepresentationTheory.Tensors.TensorVolumeSplit

/-! Unbalanced actual color coefficients with excess vector degree divisible
by three are spanned by permutations followed by determinant contractions. -/
namespace Math.SU3VolumeContractions
set_option autoImplicit false
noncomputable section
open Representation SL3ColorPlanes SL3CompactComparison
open scoped TensorProduct

@[reducible] local instance (A : Type*) [AddCommGroup A] [Module ℂ A] (n : ℕ) :
    AddCommGroup (⨂[ℂ]^n A) := inferInstance
@[reducible] local instance (a b : ℕ) : AddCommGroup (MixedCarrier a b) := inferInstance

def basis : Module.Basis (Fin 3) ℂ Vector := Pi.basisFun ℂ (Fin 3)

theorem determinant (g : Group) : LinearMap.det (standard g) = 1 := by
  change LinearMap.det (Matrix.toLin' g.val) = 1
  rw [LinearMap.det_toLin']
  exact g.property

def volumeSplit (q k : ℕ) := TensorVolumeSplit.raiseDegree standard basis determinant q k

def permutation (n : ℕ) (sigma : Equiv.Perm (Fin n)) :
    IntertwiningMap (standard.tensorPower n) (standard.tensorPower n) where
  toLinearMap := TauCeti.permTensorAction ℂ 3 n sigma
  isIntertwining' g := by
    exact (TauCeti.commute_permTensorAction_tensorPowerRep ℂ 3 n sigma
      (Matrix.SpecialLinearGroup.toGL g)).eq

theorem hom_image (q k : ℕ)
    (f : IntertwiningMap (standard.tensorPower (q+3*k)) (standard.tensorPower q)) :
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin (q+3*k))),
      f.toLinearMap = (volumeSplit q k).project.toLinearMap ∘ₗ
        TauCeti.permTensorActionAlgHom ℂ 3 (q+3*k) a := by
  let e := (volumeSplit q k).embed.comp f
  obtain ⟨a,ha⟩ := SL3TensorCommutant.permutation_image (q+3*k) e.toLinearMap
    (fun g => e.isIntertwining' g)
  refine ⟨a,?_⟩
  rw [ha]
  apply LinearMap.ext
  intro x
  exact ((volumeSplit q k).left_inv (f x)).symm

def complexContraction (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k))) :
    InvariantCoefficientTransport.Invariants (mixed (q+3*k) q) :=
  (TensorPowerDualEquivalence.curry standard (q+3*k) q).symm
    ((volumeSplit q k).project.comp (permutation (q+3*k) sigma))

def contraction (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k))) :
    InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed (q+3*k) q) where
  toLinearMap := (complexContraction q k sigma).toLinearMap
  isIntertwining' u := by
    apply LinearMap.ext
    intro x
    have he := (complexContraction q k sigma).isIntertwining _ _ (compactInclusion u) x
    have hm := congrArg (fun r => r u) (mixed_compact (q+3*k) q)
    exact hm ▸ he

theorem contraction_apply (q k : ℕ) (sigma : Equiv.Perm (Fin (q+3*k)))
    (x : ⨂[ℂ]^(q+3*k) Vector) (y : ⨂[ℂ]^q (Module.Dual ℂ Vector)) :
    contraction q k sigma (x ⊗ₜ[ℂ] y) =
      TensorPowerDualEquivalence.equivalence standard q y
        ((volumeSplit q k).project (TauCeti.permTensorAction ℂ 3 (q+3*k) sigma x)) := by
  have he := TensorPowerDualEquivalence.curry_apply standard (q+3*k) q
    (complexContraction q k sigma) x y
  rw [show TensorPowerDualEquivalence.curry standard (q+3*k) q
      (complexContraction q k sigma) =
        (volumeSplit q k).project.comp (permutation (q+3*k) sigma) from
    (TensorPowerDualEquivalence.curry standard (q+3*k) q).apply_symm_apply _] at he
  exact he.symm

theorem formula (q k : ℕ)
    (f : InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed (q+3*k) q)) :
    ∃ a : MonoidAlgebra ℂ (Equiv.Perm (Fin (q+3*k))),
      ∀ (x : ⨂[ℂ]^(q+3*k) Vector) (y : ⨂[ℂ]^q (Module.Dual ℂ Vector)),
        f (x ⊗ₜ[ℂ] y) = TensorPowerDualEquivalence.equivalence standard q y
          ((volumeSplit q k).project (TauCeti.permTensorActionAlgHom ℂ 3 (q+3*k) a x)) := by
  let F := TensorPowerDualEquivalence.curry standard (q+3*k) q
    (SU3BalancedContractions.extend (q+3*k) q f)
  obtain ⟨a,ha⟩ := hom_image q k F
  refine ⟨a,?_⟩
  intro x y
  have he := TensorPowerDualEquivalence.curry_apply standard (q+3*k) q
    (SU3BalancedContractions.extend (q+3*k) q f) x y
  change TensorPowerDualEquivalence.equivalence standard q y (F.toLinearMap x) = f (x ⊗ₜ[ℂ] y) at he
  rw [ha] at he
  exact he.symm

/-- Every compact coefficient lies in the span of the explicit contractions. -/
theorem spanning (q k : ℕ)
    (f : InvariantCoefficientTransport.Invariants (SU3TensorPositive.mixed (q+3*k) q)) :
    ∃ c : Equiv.Perm (Fin (q+3*k)) → ℂ,
      f = ∑ sigma, c sigma • contraction q k sigma := by
  obtain ⟨a,ha⟩ := formula q k f
  refine ⟨a.coeff,?_⟩
  apply IntertwiningMap.ext
  apply TensorProduct.ext'
  intro x y
  change f (x ⊗ₜ[ℂ] y) = (∑ sigma, a.coeff sigma • contraction q k sigma) (x ⊗ₜ[ℂ] y)
  rw [ha,TauCeti.permTensorActionAlgHom_eq_sum]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    IntertwiningMap.sum_apply,IntertwiningMap.smul_apply,contraction_apply]

end
end Math.SU3VolumeContractions
