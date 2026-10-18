import Physics.StandardModel.Operators.DuueResidualCompleteness
import Math.RepresentationTheory.InvariantFunctionalCoordinates

open Math

namespace GUT.HeeckLeDuueCertificate
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor DuueOrderedCompleteness SMEpsilonTensor
open scoped TensorProduct
variable {H U D E : Type*} [Group H] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup E] [Module ℂ E]
  (u : Representation ℂ H U) (d : Representation ℂ H D) (e : Representation ℂ H E)
local instance : AddCommGroup ((Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] D) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((ℂ ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] E) :=
  Module.addCommMonoidToAddCommGroup ℂ

/-- D,U,U,E to U,U,D,E is even; reversing the first epsilon gives -1.
The source swap is fixed by the exterior reconstruction, not an assumption. -/
def seedCoordinates (k : Residual u d e) : Fin 2 → Residual u d e :=
  ![0, -DuueResidualCompleteness.swap u d e k]
def ordered (k : Residual u d e) := (homEquiv u d e).symm (seedCoordinates u d e k)

theorem ordered_apply (k : Residual u d e) (a b c : Color) (z : ℂ)
    (s t v w : WeylSpinor.Space) (x y : U) (h : D) (j : E) :
    ordered u d e k
      ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        (((c ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] ((z ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] j))) =
      z * (eps3 c a b * FourDoubletInvariant.eps v s *
        FourDoubletInvariant.eps t w *
        k ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))) := by
  rw [ordered, assemble_apply]
  simp [seedCoordinates, DuueResidualCompleteness.swap_apply, eps3,
    FourDoubletInvariant.eps]
  ring

def candidate (k : Residual u d e) : DuueExchange.Sector u d e :=
  ⟨FourSlotAlternation.coefficient (external upSpin u) (external downSpin d)
    (external electronSpin e) (ordered u d e k),
    FourSlotSpeciesDegree.coefficient_hasDegree _ _ _ _⟩

theorem restriction_candidate (k : Residual u d e) :
    FourSlotRestrictionLift.restriction (external upSpin u) (external downSpin d)
      (external electronSpin e) (candidate u d e k).val =
    (homEquiv u d e).symm (DuueResidualCompleteness.complete u d e k).val := by
  apply IntertwiningMap.ext
  repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
  rename_i a s x b t y c v h z w j
  let X := ((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x)
  let Y := ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)
  let Z := ((c ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] h)
  let W := ((z ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] j)
  change FourSlotRestrictionLift.linearRestriction _ _ _ (candidate u d e k).val
    ((X ⊗ₜ[ℂ] Y) ⊗ₜ[ℂ] (Z ⊗ₜ[ℂ] W)) =
      (homEquiv u d e).symm (DuueResidualCompleteness.complete u d e k).val
        ((X ⊗ₜ[ℂ] Y) ⊗ₜ[ℂ] (Z ⊗ₜ[ℂ] W))
  rw [FourSlotRestrictionLift.linearRestriction_apply]
  change FourSlotAlternation.coefficient _ _ _ (ordered u d e k)
    (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots X Y Z W)) = _
  erw [FourSlotAlternation.coefficient_slots]
  change (homEquiv u d e).symm (seedCoordinates u d e k)
    ((X ⊗ₜ[ℂ] Y) ⊗ₜ[ℂ] (Z ⊗ₜ[ℂ] W)) -
    (homEquiv u d e).symm (seedCoordinates u d e k)
    ((Y ⊗ₜ[ℂ] X) ⊗ₜ[ℂ] (Z ⊗ₜ[ℂ] W)) = _
  dsimp only [X,Y,Z,W]
  rw [assemble_apply, assemble_apply, assemble_apply]
  have hc : eps3 b a c = -eps3 a b c := by unfold eps3; ring
  rw [hc]
  simp only [seedCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
    DuueResidualCompleteness.complete]
  simp [DuueResidualCompleteness.swap_apply, FourDoubletInvariant.eps]
  ring

theorem candidate_eq (k : Residual u d e) :
    candidate u d e k = (DuueResidualCompleteness.homEquiv u d e).symm k := by
  apply (DuueResidualCompleteness.homEquiv u d e).injective
  rw [LinearEquiv.apply_symm_apply]
  change (homEquiv u d e
    (FourSlotRestrictionLift.restriction _ _ _ (candidate u d e k).val)) 0 = k
  rw [restriction_candidate, LinearEquiv.apply_symm_apply]
  rfl

theorem extract_candidate (k : Residual u d e) :
    DuueResidualCompleteness.homEquiv u d e (candidate u d e k) = k := by
  rw [candidate_eq, LinearEquiv.apply_symm_apply]
theorem candidate_extract (f : DuueExchange.Sector u d e) :
    candidate u d e (DuueResidualCompleteness.homEquiv u d e f) = f := by
  rw [candidate_eq, LinearEquiv.symm_apply_apply]

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  (bU : Module.Basis I ℂ U) (bD : Module.Basis J ℂ D) (bE : Module.Basis K ℂ E)
def tensorBasis := (bU.tensorProduct bU).tensorProduct (bD.tensorProduct bE)
def finiteEquiv := (DuueResidualCompleteness.homEquiv u d e).trans
  (InvariantFunctionalCoordinates.equiv (flavor u d e) (tensorBasis bU bD bE))

def flavorEquiv (hr : ∀ g, flavor u d e g = 1) :
    DuueExchange.Sector u d e ≃ₗ[ℂ] ((I × I) × (J × K) → ℂ) :=
  (DuueResidualCompleteness.homEquiv u d e).trans
    (InvariantFunctionalCoordinates.unrestrictedEquiv _ (tensorBasis bU bD bE) hr)
def flavorBasis (hr : ∀ g, flavor u d e g = 1) :=
  Module.Basis.ofEquivFun (flavorEquiv u d e bU bD bE hr)

theorem flavorBasis_independent (hr : ∀ g, flavor u d e g = 1) :
    LinearIndependent ℂ (flavorBasis u d e bU bD bE hr) :=
  (flavorBasis u d e bU bD bE hr).linearIndependent
theorem flavorBasis_spans (hr : ∀ g, flavor u d e g = 1) :
    Submodule.span ℂ (Set.range (flavorBasis u d e bU bD bE hr)) = ⊤ :=
  (flavorBasis u d e bU bD bE hr).span_eq
theorem flavorBasis_is_candidate (hr : ∀ g, flavor u d e g = 1)
    (i : (I × I) × (J × K)) :
    candidate u d e (DuueResidualCompleteness.homEquiv u d e
      (flavorBasis u d e bU bD bE hr i)) =
      flavorBasis u d e bU bD bE hr i := candidate_extract _ _ _ _

include bU bD bE in
theorem flavor_finrank (hr : ∀ g, flavor u d e g = 1) :
    Module.finrank ℂ (DuueExchange.Sector u d e) =
      Fintype.card I * Fintype.card I * (Fintype.card J * Fintype.card K) := by
  rw [(flavorEquiv u d e bU bD bE hr).finrank_eq]
  simp

omit [Fintype I] [Fintype J] [Fintype K] in
theorem finite_inverse_is_candidate
    (c : InvariantFunctionalCoordinates.space (flavor u d e) (tensorBasis bU bD bE)) :
    (finiteEquiv u d e bU bD bE).symm c =
      candidate u d e ((InvariantFunctionalCoordinates.equiv _ _).symm c) := by
  rw [candidate_eq]; rfl
end
end GUT.HeeckLeDuueCertificate
