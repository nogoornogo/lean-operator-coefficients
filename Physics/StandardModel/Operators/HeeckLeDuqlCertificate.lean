import Physics.StandardModel.Operators.DuqlExteriorCompleteness
import Math.RepresentationTheory.InvariantFunctionalCoordinates

open Math

namespace GUT.HeeckLeDuqlCertificate
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor DuqlOrderedCompleteness SMEpsilonTensor
open scoped TensorProduct
universe v
variable {H : Type*} {D U Q L : Type v} [Group H]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup L] [Module ℂ L]
  (d : Representation ℂ H D) (u : Representation ℂ H U)
  (q : Representation ℂ H Q) (l : Representation ℂ H L)

/-- Direct gauge/Lorentz contraction with the residual functional, before
exterior descent, in the D,U,Q,L order of Heeck–Le Section 6. -/
def ordered (k : Residual d u q l) : Coefficient d u q l :=
  (coefficient localContraction k).comp (regroup d u q l).toIntertwiningMap

theorem ordered_eq (k : Residual d u q l) :
    ordered d u q l k = (homEquiv d u q l).symm k := rfl

theorem ordered_apply (k : Residual d u q l)
    (a b c : Color) (w v : Weak) (s t x y : WeylSpinor.Space)
    (f : D) (g : U) (h : Q) (j : L) :
    ordered d u q l k
      ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] f) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] g)) ⊗ₜ[ℂ]
        ((((c ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ]
          ((v ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] j))) =
      eps3 a b c * eps2 w v * (eps2 s t * eps2 x y) *
        k ((f ⊗ₜ[ℂ] g) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) := by
  change eps3 a b c * eps2 w v * (eps2 x y * eps2 s t) *
    k ((f ⊗ₜ[ℂ] g) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) = _
  ring

def candidate (k : Residual d u q l) : DuqlExteriorCompleteness.Sector d u q l :=
  DistinctSpeciesAlternation.descend _
    (DistinctSpeciesAlternation.invariantEquiv _
      ((FourTensorMultilinear.invariantEquiv _).symm (ordered d u q l k)))

theorem candidate_eq (k : Residual d u q l) :
    candidate d u q l k = (DuqlExteriorCompleteness.homEquiv d u q l).symm k := rfl

theorem extract_candidate (k : Residual d u q l) :
    DuqlExteriorCompleteness.homEquiv d u q l (candidate d u q l k) = k := by
  rw [candidate_eq, LinearEquiv.apply_symm_apply]
theorem candidate_extract (f : DuqlExteriorCompleteness.Sector d u q l) :
    candidate d u q l (DuqlExteriorCompleteness.homEquiv d u q l f) = f := by
  rw [candidate_eq, LinearEquiv.symm_apply_apply]

variable {I J K N : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype N]
  (bD : Module.Basis I ℂ D) (bU : Module.Basis J ℂ U)
  (bQ : Module.Basis K ℂ Q) (bL : Module.Basis N ℂ L)
def tensorBasis := (bD.tensorProduct bU).tensorProduct (bQ.tensorProduct bL)
def finiteEquiv := (DuqlExteriorCompleteness.homEquiv d u q l).trans
  (InvariantFunctionalCoordinates.equiv (flavor d u q l) (tensorBasis bD bU bQ bL))

/-- Trivial residual action is an extra hypothesis, not inferred from dimensions. -/
def flavorEquiv (hr : ∀ g, flavor d u q l g = 1) :
    DuqlExteriorCompleteness.Sector d u q l ≃ₗ[ℂ] ((I × J) × (K × N) → ℂ) :=
  (DuqlExteriorCompleteness.homEquiv d u q l).trans
    (InvariantFunctionalCoordinates.unrestrictedEquiv _ (tensorBasis bD bU bQ bL) hr)

def flavorBasis (hr : ∀ g, flavor d u q l g = 1) :=
  Module.Basis.ofEquivFun (flavorEquiv d u q l bD bU bQ bL hr)

theorem flavorBasis_independent (hr : ∀ g, flavor d u q l g = 1) :
    LinearIndependent ℂ (flavorBasis d u q l bD bU bQ bL hr) :=
  (flavorBasis d u q l bD bU bQ bL hr).linearIndependent
theorem flavorBasis_spans (hr : ∀ g, flavor d u q l g = 1) :
    Submodule.span ℂ (Set.range (flavorBasis d u q l bD bU bQ bL hr)) = ⊤ :=
  (flavorBasis d u q l bD bU bQ bL hr).span_eq
theorem flavorBasis_is_candidate (hr : ∀ g, flavor d u q l g = 1)
    (i : (I × J) × (K × N)) :
    candidate d u q l (DuqlExteriorCompleteness.homEquiv d u q l
      (flavorBasis d u q l bD bU bQ bL hr i)) =
      flavorBasis d u q l bD bU bQ bL hr i := candidate_extract _ _ _ _ _

include bD bU bQ bL in
theorem flavor_finrank (hr : ∀ g, flavor d u q l g = 1) :
    Module.finrank ℂ (DuqlExteriorCompleteness.Sector d u q l) =
      Fintype.card I * Fintype.card J * (Fintype.card K * Fintype.card N) := by
  rw [(flavorEquiv d u q l bD bU bQ bL hr).finrank_eq]
  simp

omit [Fintype I] [Fintype J] [Fintype K] [Fintype N] in
theorem finite_inverse_is_candidate
    (c : InvariantFunctionalCoordinates.space (flavor d u q l) (tensorBasis bD bU bQ bL)) :
    (finiteEquiv d u q l bD bU bQ bL).symm c =
      candidate d u q l ((InvariantFunctionalCoordinates.equiv _ _).symm c) := by
  rw [candidate_eq]; rfl
end
end GUT.HeeckLeDuqlCertificate
