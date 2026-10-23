import Physics.StandardModel.Operators.BaryonOne.Qqql.HeeckLeQqqlConvention
import Physics.StandardModel.Operators.BaryonOne.Qqql.QqqlFiniteFlavor
import Math.RepresentationTheory.Tensors.FourSlotTripleOrbit

open Math

/-! Exterior descent of the literal Heeck–Le Q³L seed, with explicit symmetry-component
normalization. This is a local derivative-free certificate, not an amplitude API. -/
namespace Physics.HeeckLeQqqlCertificate
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor QqqlOrderedCompleteness
  SMEpsilonTensor FourDoubletProductExchange FourDoubletProductComponents
  HeeckLeQqqlConvention
open scoped TensorProduct
variable {H Q L : Type*} [Group H] [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup L] [Module ℂ L]
  (q : Representation ℂ H Q) (l : Representation ℂ H L)

local instance : AddCommGroup (((Color ⊗[ℂ] Weak) ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] Q) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((Weak ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] L) :=
  Module.addCommMonoidToAddCommGroup ℂ

def seedFamily (f : QqqlExchange.Residual q l) : Fin 2 × Fin 2 → QqqlExchange.Residual q l :=
  fun ij => seed ij.1 ij.2 • f

def orderedSeed (f : QqqlExchange.Residual q l) :=
  (homEquiv q l).symm (seedFamily q l f)

theorem orderedSeed_apply (f : QqqlExchange.Residual q l)
    (a b c : Color) (v0 v1 v2 v3 : Weak) (s0 s1 s2 s3 : WeylSpinor.Space)
    (x y z : Q) (h : L) :
    (orderedSeed q l f).toLinearMap
      (((((a ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] s0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((b ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        ((((c ⊗ₜ[ℂ] v2) ⊗ₜ[ℂ] s2) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ]
          ((v3 ⊗ₜ[ℂ] s3) ⊗ₜ[ℂ] h))) =
      eps3 a b c * f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] h)) *
        evaluate seed v0 v1 v2 v3 s0 s1 s2 s3 := by
  change (homEquiv q l).symm (seedFamily q l f) _ = _
  rw [assemble_apply]
  simp [seedFamily, evaluate, seed]
  ring

/-- The candidate is genuinely raw exterior alternatization of the printed
local seed, not defined as an inverse of the completeness equivalence. -/
def candidate (f : QqqlFlavorComponents.residualSpace q l) :
    QqqlExteriorCompleteness.Sector q l :=
  ⟨FourSlotTripleAlternation.coefficient (external quarkSpin q) (external leptonSpin l)
    (orderedSeed q l (source q l f)),
    FourSlotTripleSector.coefficient_hasDegree (external quarkSpin q)
      (external leptonSpin l) (orderedSeed q l (source q l f))⟩

theorem evaluate_orbit (a b c d e f : ℂ)
    (v0 v1 v2 v3 s0 s1 s2 s3 : FourDoubletInvariant.Space) :
    evaluate (orbit a b c d e f) v0 v1 v2 v3 s0 s1 s2 s3 =
      a * evaluate seed v0 v1 v2 v3 s0 s1 s2 s3 +
      b * evaluate seed v1 v0 v2 v3 s1 s0 s2 s3 +
      c * evaluate seed v0 v2 v1 v3 s0 s2 s1 s3 +
      d * evaluate seed v1 v2 v0 v3 s1 s2 s0 s3 +
      e * evaluate seed v2 v0 v1 v3 s2 s0 s1 s3 +
      f * evaluate seed v2 v1 v0 v3 s2 s1 s0 s3 := by
  simp [orbit, evaluate, seed, exchange01, exchange12, FourDoubletInvariant.eps, smul_eq_mul]
  ring

theorem restriction_candidate (f : QqqlFlavorComponents.residualSpace q l) :
    FourSlotTripleRestriction.restriction (external quarkSpin q) (external leptonSpin l)
      (candidate q l f).val =
      (QqqlExteriorCompleteness.coordinates q l).symm (assembleModule f.val) := by
  apply IntertwiningMap.ext
  repeat first | apply TensorProduct.ext | apply LinearMap.ext; intro
  rename_i a v0 s0 x b v1 s1 y c v2 s2 z v3 s3 h
  let X := (((a ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] s0) ⊗ₜ[ℂ] x)
  let Y := (((b ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] s1) ⊗ₜ[ℂ] y)
  let Z := (((c ⊗ₜ[ℂ] v2) ⊗ₜ[ℂ] s2) ⊗ₜ[ℂ] z)
  let W := ((v3 ⊗ₜ[ℂ] s3) ⊗ₜ[ℂ] h)
  change FourSlotTripleRestriction.linearRestriction _ _ (candidate q l f).val
      ((X ⊗ₜ[ℂ] Y) ⊗ₜ[ℂ] (Z ⊗ₜ[ℂ] W)) =
    (homEquiv q l).symm (fun ij => assembleModule f.val ij.1 ij.2)
      ((X ⊗ₜ[ℂ] Y) ⊗ₜ[ℂ] (Z ⊗ₜ[ℂ] W))
  rw [FourSlotTripleRestriction.linearRestriction_apply]
  change exteriorPower.alternatingMapLinearEquiv
    (FourSlotTripleAlternation.alternating (orderedSeed q l (source q l f)).toLinearMap)
    (exteriorPower.ιMulti ℂ 4 (FourSlotTripleAlternation.slots X Y Z W)) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    FourSlotTripleAlternation.alternating_slots_orbit]
  dsimp only [X, Y, Z, W]
  rw [orderedSeed_apply, orderedSeed_apply, orderedSeed_apply,
    orderedSeed_apply, orderedSeed_apply, orderedSeed_apply, assemble_apply]
  change _ = eps3 a b c * evaluate
    (QqqlExchange.values q l (assembleModule f.val) x y z h)
    v0 v1 v2 v3 s0 s1 s2 s3
  rw [QqqlFlavorComponents.values_assemble, ← source_orbit, evaluate_orbit]
  have h01 : eps3 b a c = -eps3 a b c := by unfold eps3; ring
  have h12 : eps3 a c b = -eps3 a b c := by unfold eps3; ring
  have h123 : eps3 b c a = eps3 a b c := by unfold eps3; ring
  have h132 : eps3 c a b = eps3 a b c := by unfold eps3; ring
  have h13 : eps3 c b a = -eps3 a b c := by unfold eps3; ring
  rw [h01, h12, h123, h132, h13]
  ring

/-- Literal seed descent realizes the complete inverse, with the source
normalization fixed rather than assumed. -/
theorem candidate_eq (f : QqqlFlavorComponents.residualSpace q l) :
    candidate q l f = (QqqlFlavorComponents.exteriorEquiv q l).symm f := by
  apply (QqqlFlavorComponents.exteriorEquiv q l).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  change extractModule (QqqlExteriorCompleteness.coordinates q l
    (FourSlotTripleRestriction.restriction (external quarkSpin q)
      (external leptonSpin l) (candidate q l f).val)) = f.val
  rw [restriction_candidate, LinearEquiv.apply_symm_apply]
  exact moduleEquiv.apply_symm_apply f.val

theorem every_sector_is_candidate (f : QqqlExteriorCompleteness.Sector q l) :
    candidate q l (QqqlFlavorComponents.exteriorEquiv q l f) = f := by
  rw [candidate_eq, LinearEquiv.symm_apply_apply]

theorem candidate_injective : Function.Injective (candidate q l) := by
  intro f g h
  apply (QqqlFlavorComponents.exteriorEquiv q l).symm.injective
  simpa only [candidate_eq] using h

end
end Physics.HeeckLeQqqlCertificate
