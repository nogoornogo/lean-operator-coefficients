import Physics.StandardModel.Operators.QquePhysicalExteriorCompleteness

open Math

/-! Heeck–Le 2604.25134v2 Section 6, in physical Q,Q,U,E order.
The bracket normalization is the existing algebraic Weyl epsilon convention. -/
namespace GUT.HeeckLeQqueCertificate
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor QquePhysicalOrderedCompleteness SMEpsilonTensor
open scoped TensorProduct
variable {H Q U E : Type*} [Group H]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ H Q) (u : Representation ℂ H U) (e : Representation ℂ H E)

local instance : AddCommGroup (((Color ⊗[ℂ] Weak) ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] Q) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((Color ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] U) :=
  Module.addCommMonoidToAddCommGroup ℂ
local instance : AddCommGroup ((ℂ ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ] E) :=
  Module.addCommMonoidToAddCommGroup ℂ

def ordered (k : Residual q u e) : Coefficient q u e :=
  (coefficient localContraction k).comp (regroup q u e).toIntertwiningMap

theorem literal (k : Residual q u e) (a b c : Color) (v w : Weak)
    (s t h j : WeylSpinor.Space) (x y : Q) (z : U) (r : E) (m : ℂ) :
    ordered q u e k
      (((((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        (((c ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((m ⊗ₜ[ℂ] j) ⊗ₜ[ℂ] r))) =
      eps3 a b c * eps2 v w * m * (eps2 s t * eps2 h j) *
        k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r)) :=
  assemble_apply q u e k a b c v w s t h j x y z r m

/-- Exterior lift of the literal ordered contraction, with the factor 1/2
already fixed in the independent repeated-species lift. -/
def candidate (k : QquePhysicalExteriorCompleteness.residualSpace q u e) :
    QquePhysicalExteriorCompleteness.Sector q u e :=
  (QquePhysicalExteriorCompleteness.exteriorEquiv q u e).symm k

theorem restriction_candidate (k : QquePhysicalExteriorCompleteness.residualSpace q u e) :
    FourSlotRestrictionLift.restriction (external quarkSpin q) (external upSpin u)
      (external electronSpin e) (candidate q u e k).val = ordered q u e k.val := by
  have h := (QquePhysicalExteriorCompleteness.exteriorEquiv q u e).apply_symm_apply k
  apply (homEquiv q u e).injective
  change (homEquiv q u e) _ = (homEquiv q u e) ((homEquiv q u e).symm k.val)
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg Subtype.val h

theorem extract_candidate (k : QquePhysicalExteriorCompleteness.residualSpace q u e) :
    QquePhysicalExteriorCompleteness.exteriorEquiv q u e (candidate q u e k) = k :=
  LinearEquiv.apply_symm_apply _ _

theorem candidate_extract (f : QquePhysicalExteriorCompleteness.Sector q u e) :
    candidate q u e (QquePhysicalExteriorCompleteness.exteriorEquiv q u e f) = f :=
  LinearEquiv.symm_apply_apply _ _

end
end GUT.HeeckLeQqueCertificate
