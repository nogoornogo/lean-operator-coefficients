import GUT.SU6.SelectionRules.Models.CovariantFourFermion
import Math.RepresentationTheory.Constructions.PointwiseGaugeRemoval

open Physics

/-! Gauge comparison on the supported fourth exterior power of actual light
fields. This does not construct Lorentz/SM BNV support. -/
namespace GUT.GaugeEquivalentCandidate
set_option autoImplicit false
noncomputable section
open Math Representation AutomorphismCovariantModel
variable {H K : Type*} [CommGroup H] [TopologicalSpace H]
  [Group K] [TopologicalSpace K] (M : Model H K)
  (S : CovariantFourFermion.Support M)

abbrev localAction := AutomorphismCovariantExterior.localQuotient
  M.mass.radical.toRepresentation M.beta (lightAction M) S
abbrev action := AutomorphismCovariantExterior.supportedAction
  M.mass.radical.toRepresentation M.beta (lightAction M) S

/-- The gauge factors must belong to the actual unbroken group K. -/
theorem removed_projection (s : H → K) (h : H)
    (v : (⋀[ℂ]^4 M.mass.radical.toSubmodule) ⧸ S.unsupported) :
    PointwiseGaugeRemoval.projection (localAction M S)
      (PointwiseGaugeRemoval.removed (localAction M S) M.beta (action M S) s h v) =
    (AutomorphismCovariantHom.quotient (localAction M S) M.beta (action M S)) h
      (PointwiseGaugeRemoval.projection (localAction M S) v) :=
  PointwiseGaugeRemoval.removed_projection _ _ _ _ _ _

/-- A genuine reference action and checked local gauge comparison transfer
prohibition; no UV compensator outside K is implicitly permitted. -/
theorem forbidden_iff (gamma : H →* MulAut K)
    (B : AutomorphismCovariantHom.Action (localAction M S) gamma)
    (s : H → K)
    (hs : ∀ h v, (action M S).residual h v = (localAction M S) (s h) (B.residual h v)) :
    (∀ f : LocalCoinvariantHom.invariantHom (localAction M S)
      (action M S).residual (trivial ℂ H ℂ), f = 0) ↔
    ∀ f : LocalCoinvariantHom.invariantHom (localAction M S)
      B.residual (trivial ℂ H ℂ), f = 0 :=
  PointwiseGaugeRemoval.forbidden_iff _ _ _ _ _ s hs
/-- Transfer from independently defined original supported coefficients. -/
theorem input_forbidden_iff (gamma : H →* MulAut K)
    (B : AutomorphismCovariantHom.Action (localAction M S) gamma)
    (s : H → K)
    (hs : ∀ h v, (action M S).residual h v = (localAction M S) (s h) (B.residual h v)) :
    (∀ f : CovariantFourFermion.Input M S, f = 0) ↔
    ∀ f : LocalCoinvariantHom.invariantHom (localAction M S)
      B.residual (trivial ℂ H ℂ), f = 0 :=
  ((CovariantFourFermion.input_forbidden_iff M S).trans
    (CovariantFourFermion.forbidden_iff M S).symm).trans
    (forbidden_iff M S gamma B s hs)

end
end GUT.GaugeEquivalentCandidate
