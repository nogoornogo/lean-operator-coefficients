import Math.RepresentationTheory.Content.PatternMultiplicityEquiv
import Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel

/-! Actual local ranks depend on species multiplicities, not word order. -/
namespace Physics.SMRankMultiplicity
set_option autoImplicit false
noncomputable section
open Math Representation
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p q : Fin n → DeltaLOneSignedInput.Species)
  (h : ∀ s, (Finset.univ.filter (fun i => p i = s)).card =
    (Finset.univ.filter (fun i => q i = s)).card)
  (m : ℕ) (delta : ℤ)

def sourceEquiv : Representation.Equiv (SMIntegralLocalWeights.source flavor p)
    (SMIntegralLocalWeights.source flavor q) where
  toLinearEquiv := (PatternMultiplicityEquiv.equiv (DeltaLOneSignedFields.field flavor) p q h).toLinearEquiv
  isIntertwining' g := (PatternMultiplicityEquiv.equiv
    (DeltaLOneSignedFields.field flavor) p q h).isIntertwining' (g,1)

def actionEquiv : Representation.Equiv (SMIntegralLocalWeights.action flavor p m delta)
    (SMIntegralLocalWeights.action flavor q m delta) :=
  ExternalInvariantTensor.tensorEquiv (sourceEquiv flavor p q h)
    (Representation.Equiv.refl (SMIntegralLocalWeights.boson (H := H) m delta))

def kernelEquiv : SMFullLocalKernel.Kernel flavor p m delta ≃ₗ[ℂ]
    SMFullLocalKernel.Kernel flavor q m delta :=
  ((SMFullLocalKernel.coefficientEquiv flavor p m delta).symm.trans
    (InvariantCoefficientTransport.alongEquiv (actionEquiv flavor p q h m delta))).trans
    (SMFullLocalKernel.coefficientEquiv flavor q m delta)

include h in
theorem rank_eq : Module.finrank ℂ
    (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor q m delta)) := by
  have hk := (kernelEquiv flavor p q h m delta).finrank_eq
  have hd := (actionEquiv flavor p q h m delta).toLinearEquiv.finrank_eq
  have hp := LinearMap.finrank_range_add_finrank_ker (SMFullLocalKernel.constraints flavor p m delta)
  have hq := LinearMap.finrank_range_add_finrank_ker (SMFullLocalKernel.constraints flavor q m delta)
  simp only [Module.finrank_pi, Fintype.card_fin] at hp hq
  change Module.finrank ℂ (LinearMap.ker (SMFullLocalKernel.constraints flavor p m delta)) =
    Module.finrank ℂ (LinearMap.ker (SMFullLocalKernel.constraints flavor q m delta)) at hk
  change Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m) =
    Module.finrank ℂ (SMFullLocalKernel.Carrier flavor q m) at hd
  exact Nat.add_right_cancel (hp.trans (hd.trans (hq.symm.trans
    (congrArg (fun t => Module.finrank ℂ
      (LinearMap.range (SMFullLocalKernel.constraints flavor q m delta)) + t) hk.symm))))

end
end Physics.SMRankMultiplicity
