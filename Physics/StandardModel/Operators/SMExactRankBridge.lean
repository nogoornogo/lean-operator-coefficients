import Math.LinearAlgebra.ExactRankCertificate
import Physics.StandardModel.Operators.SMFullLocalKernel

/-! Conditional consumer of exact rank certificates, with the semantic bridge explicit. -/
namespace GUT.SMExactRankBridge
set_option autoImplicit false
open Math
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species) (m : ℕ) (delta : ℤ)
  {I J T : Type*} [Fintype I] [Fintype J] [Fintype T] [DecidableEq T]
  (A : Matrix I J ℚ) (c : ExactRankCertificate.Certificate (T := T) A)

include c in
/-- A rational matrix is useful only after proving it describes the actual coefficients. -/
theorem rank_from_certificate
    (e : InvariantCoefficientTransport.Invariants (SMIntegralLocalWeights.action flavor p m delta)
      ≃ₗ[ℂ] LinearMap.ker (A.map (Rat.castHom ℂ)).mulVecLin) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
      Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m) -
        (Fintype.card J - Fintype.card T) := by
  have ek := (SMFullLocalKernel.coefficientEquiv flavor p m delta).symm.trans e
  have hk := ek.finrank_eq.trans (ExactRankCertificate.mapped_nullity c (Rat.castHom ℂ))
  have h := LinearMap.finrank_range_add_finrank_ker (SMFullLocalKernel.constraints flavor p m delta)
  change Module.finrank ℂ (LinearMap.ker (SMFullLocalKernel.constraints flavor p m delta)) = _ at hk
  simp only [Module.finrank_pi, Fintype.card_fin] at h
  have he : Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) +
      (Fintype.card J - Fintype.card T) =
      Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m) :=
    (congrArg (fun t => Module.finrank ℂ
      (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) + t) hk.symm).trans h
  exact Nat.eq_sub_of_add_eq he

end GUT.SMExactRankBridge
