import Physics.StandardModel.Gauge.QqueGaugeUniqueness
import Physics.FieldTheory.Spinor.WeylSpinorUniqueness
import Math.RepresentationTheory.NormalizedInvariantFactor
import Math.RepresentationTheory.InvariantCoefficientTransport

open Math

/-! The qque ordered invariant space in the shared `(gauge × spin) × residual`
convention. Multiplicities are arbitrary carriers, not implicitly duals. -/
namespace GUT.QquePhysicalOrderedCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct

def spin := (WeylSpinor.left.tprod WeylSpinor.left).tprod
  (WeylSpinor.right.tprod WeylSpinor.right)
def spinWitness := (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ]
  (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1)
def localRepresentation := external qqueRepresentation spin
def localContraction := coefficient qqueIntertwiner WeylSpinor.four
def localWitness := qqueWitness ⊗ₜ[ℂ] spinWitness

theorem local_normalized : localContraction localWitness = 1 := by
  change qque qqueWitness * WeylSpinor.four spinWitness = 1
  rw [qque_witness]
  norm_num [spinWitness, WeylSpinor.four, WeylSpinor.epsilonLeft,
    WeylSpinor.epsilonRight, eps2, weakBasis]

theorem local_unique (f : IntertwiningMap localRepresentation
    (Representation.trivial ℂ (GaugeGroup × WeylSpinor.Group) ℂ)) :
    f = f localWitness • localContraction :=
  NormalizedInvariantFactor.product_unique _ _ _ _ _ _
    QqueGaugeUniqueness.eq_smul_qque WeylSpinorUniqueness.eq_smul_four f

def quarkSpin := external quark WeylSpinor.left
def upSpin := external upRight WeylSpinor.right
def electronSpin := external electronRight WeylSpinor.right
def localRegroup : Representation.Equiv
    ((quarkSpin.tprod quarkSpin).tprod (upSpin.tprod electronSpin)) localRepresentation :=
  regroupFour quark quark upRight electronRight
    WeylSpinor.left WeylSpinor.left WeylSpinor.right WeylSpinor.right

variable {R Q U E : Type*} [Group R]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ R Q) (u : Representation ℂ R U) (e : Representation ℂ R E)

abbrev flavor := (q.tprod q).tprod (u.tprod e)
def fields := ((external quarkSpin q).tprod (external quarkSpin q)).tprod
  ((external upSpin u).tprod (external electronSpin e))
abbrev Coefficient := IntertwiningMap (fields q u e)
  (Representation.trivial ℂ ((GaugeGroup × WeylSpinor.Group) × R) ℂ)
abbrev Residual := IntertwiningMap (flavor q u e) (Representation.trivial ℂ R ℂ)

def regroup : Representation.Equiv (fields q u e)
    (external localRepresentation (flavor q u e)) :=
  (regroupFour quarkSpin quarkSpin upSpin electronSpin q q u e).trans
    (externalEquiv localRegroup (Representation.Equiv.refl _))

def homEquiv : Coefficient q u e ≃ₗ[ℂ] Residual q u e :=
  (InvariantCoefficientTransport.alongEquiv (regroup q u e)).trans
    (NormalizedInvariantFactor.equiv localRepresentation (flavor q u e)
      localContraction localWitness local_normalized local_unique)

theorem assemble_apply (k : Residual q u e) (a b c : Color) (v w : Weak)
    (s t h j : WeylSpinor.Space) (x y : Q) (z : U) (r : E) (m : ℂ) :
    (homEquiv q u e).symm k
      (((((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
        (((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        (((c ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] ((m ⊗ₜ[ℂ] j) ⊗ₜ[ℂ] r))) =
      eps3 a b c * eps2 v w * m * (eps2 s t * eps2 h j) *
        k ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] r)) := by
  change qque (((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] w)) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] m)) *
    WeylSpinor.four ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) * k _ = _
  rw [qque_tmul]
  rfl

end
end GUT.QquePhysicalOrderedCompleteness
