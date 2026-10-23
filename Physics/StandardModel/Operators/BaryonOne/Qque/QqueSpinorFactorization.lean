import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior
import Physics.FieldTheory.Spinor.Weyl.WeylSpinorUniqueness
import Math.RepresentationTheory.Invariants.ExternalInvariantFactorization

open Math

/-! Exhaustive removal of the Weyl-spinor contraction with arbitrary field spectators. -/
namespace Physics.QqueSpinorFactorization
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor ExternalInvariantFactorization QqueSpinorExterior
open scoped TensorProduct

variable {K Q U E : Type*} [Group K]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ K Q) (u : Representation ℂ K U) (e : Representation ℂ K E)

def spinorWitness : (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space) ⊗[ℂ]
    (WeylSpinor.Space ⊗[ℂ] WeylSpinor.Space) :=
  (SMEpsilonTensor.weakBasis 0 ⊗ₜ[ℂ] SMEpsilonTensor.weakBasis 1) ⊗ₜ[ℂ]
    (SMEpsilonTensor.weakBasis 0 ⊗ₜ[ℂ] SMEpsilonTensor.weakBasis 1)

def regrouped (f : OrderedCoefficient q u e) :=
  f.comp (regroupFour q q u e WeylSpinor.left WeylSpinor.left
    WeylSpinor.right WeylSpinor.right).symm.toIntertwiningMap

def strip (f : OrderedCoefficient q u e) :
    IntertwiningMap ((q.tprod q).tprod (u.tprod e)) (Representation.trivial ℂ K ℂ) :=
  leftSlice _ _ (regrouped q u e f) spinorWitness

theorem reconstruct (f : OrderedCoefficient q u e) : ordered q u e (strip q u e f) = f := by
  have h := factor_right _ _ WeylSpinor.four spinorWitness
    WeylSpinorUniqueness.eq_smul_four (regrouped q u e f)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv := DFunLike.congr_fun h
    (regroupFour q q u e WeylSpinor.left WeylSpinor.left WeylSpinor.right WeylSpinor.right v)
  simpa [ordered, strip, regrouped] using hv.symm

end
end Physics.QqueSpinorFactorization
