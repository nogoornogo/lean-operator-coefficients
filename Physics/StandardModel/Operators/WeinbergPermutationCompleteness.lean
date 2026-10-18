import Physics.StandardModel.Operators.WeinbergResidualHom
import Math.RepresentationTheory.NormalizedStatisticalFactor

open Math

/-! The Weinberg exchange equation as a consumer of the common generator
statistics construction. The weak and spinor factors are exchanged together;
the local line has eigenvalue -1, hence flavor exchange has eigenvalue +1. -/
namespace GUT.WeinbergPermutationCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor WeinbergResidualHom SMEpsilonTensor
open scoped TensorProduct

def localSwap : Representation.Equiv localRepresentation localRepresentation :=
  externalEquiv
    (tensorEquiv (Representation.TensorProduct.comm _ _) (Representation.Equiv.refl _))
    (Representation.TensorProduct.comm _ _)

theorem localSwap_scalar : localContraction (localSwap localWitness) = -1 := by
  change WeinbergWeakInvariant.contraction
    ((weakBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ]
      SymmetricPower.tprod ℂ ![weakBasis 1, weakBasis 1]) *
      WeylSpinor.epsilonLeft (weakBasis 1 ⊗ₜ[ℂ] weakBasis 0) = -1
  rw [WeinbergWeakInvariant.contraction_apply]
  norm_num [WeylSpinor.epsilonLeft, eps2, weakBasis]

variable {R F : Type*} [Group R] [AddCommGroup F] [Module ℂ F]
  (a : Representation ℂ R F)

def sourceAction : Coefficient a →ₗ[ℂ] Coefficient a :=
  FiniteStatisticalFactor.sourceAction localRepresentation (a.tprod a)
    (fun _ : Unit => localSwap) (fun _ => Representation.TensorProduct.comm a a) ()

def targetAction : Residual a →ₗ[ℂ] Residual a :=
  NormalizedStatisticalFactor.targetAction localRepresentation (a.tprod a)
    localContraction localWitness (fun _ : Unit => localSwap)
    (fun _ => Representation.TensorProduct.comm a a) ()

@[simp] theorem targetAction_apply (k : Residual a) (u v : F) :
    targetAction a k (u ⊗ₜ[ℂ] v) = -k (v ⊗ₜ[ℂ] u) := by
  change localContraction (localSwap localWitness) * k (v ⊗ₜ[ℂ] u) = _
  rw [localSwap_scalar]; ring

def equiv : StatisticalCompleteness.sector (fun _ : Unit => sourceAction a) (fun _ => -1) ≃ₗ[ℂ]
    StatisticalCompleteness.sector (fun _ : Unit => targetAction a) (fun _ => -1) :=
  NormalizedStatisticalFactor.equiv localRepresentation (a.tprod a)
    localContraction localWitness local_normalized local_unique
    (fun _ : Unit => localSwap) (fun _ => Representation.TensorProduct.comm a a) (fun _ => -1)

theorem target_symmetric_iff (k : Residual a) :
    k ∈ StatisticalCompleteness.sector (fun _ : Unit => targetAction a) (fun _ => -1) ↔
      ∀ u v, k (v ⊗ₜ[ℂ] u) = k (u ⊗ₜ[ℂ] v) := by
  constructor
  · intro hk u v
    have h := congrArg (fun t : Residual a => t (u ⊗ₜ[ℂ] v)) (hk ())
    simpa using h
  · intro hk j
    ext u v
    simp [hk]

/-- The generator sector coincides with the independently defined physical
fermion-exchange condition. No assembly-image condition is substituted. -/
theorem source_sector_iff (f : Coefficient a) :
    f ∈ StatisticalCompleteness.sector (fun _ : Unit => sourceAction a) (fun _ => -1) ↔
      HasFermionExchange a f := by
  have h := StatisticalCompleteness.statistics_iff (factorEquiv a)
    (fun _ : Unit => sourceAction a) (fun _ => targetAction a) (fun _ => -1)
    (NormalizedStatisticalFactor.compatible localRepresentation (a.tprod a)
      localContraction localWitness local_normalized local_unique
      (fun _ : Unit => localSwap) (fun _ => Representation.TensorProduct.comm a a)) f
  exact h.trans ((target_symmetric_iff a _).trans (exchange_iff a f).symm)

def symmetricEquiv : sector a ≃ₗ[ℂ]
    TensorSquareMultilinear.symmetricIntertwiners a (Representation.trivial ℂ R ℂ) :=
  (ConstrainedCompleteness.Presentation.mk (factorEquiv a) (fun f =>
    (source_sector_iff a f).symm.trans
      ((StatisticalCompleteness.statistics_iff (factorEquiv a)
        (fun _ : Unit => sourceAction a) (fun _ => targetAction a) (fun _ => -1)
        (NormalizedStatisticalFactor.compatible localRepresentation (a.tprod a)
          localContraction localWitness local_normalized local_unique
          (fun _ : Unit => localSwap) (fun _ => Representation.TensorProduct.comm a a)) f).trans
        (target_symmetric_iff a _)))).equiv

theorem symmetricEquiv_agrees : symmetricEquiv a = WeinbergResidualHom.symmetricEquiv a := by
  apply LinearEquiv.ext
  intro f
  rfl

def homEquiv : sector a ≃ₗ[ℂ]
    IntertwiningMap (a.symmetricPower 2) (Representation.trivial ℂ R ℂ) :=
  (symmetricEquiv a).trans (TensorSquareMultilinear.symmetricSquareEquiv a _)

theorem homEquiv_agrees : homEquiv a = WeinbergResidualHom.homEquiv a := by
  rw [homEquiv, symmetricEquiv_agrees]
  rfl

end
end GUT.WeinbergPermutationCompleteness
