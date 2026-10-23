import Physics.StandardModel.Gauge.Tensors.DuqlGaugeUniqueness
import Physics.FieldTheory.Spinor.Weyl.WeylSpinorUniqueness
import Math.RepresentationTheory.Invariants.NormalizedInvariantFactor
import Math.RepresentationTheory.Coefficients.InvariantCoefficientTransport

open Math

/-! Ordered duql completeness with independent gauge, Lorentz and residual actions.
This is the ordered tensor interface; exterior species descent is separate. -/
namespace Physics.DuqlOrderedCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor StandardSMGaugeTensor SMEpsilonTensor
open scoped TensorProduct

def spin := (WeylSpinor.right.tprod WeylSpinor.right).tprod
  (WeylSpinor.left.tprod WeylSpinor.left)

def spinSwap : Representation.Equiv spin
    ((WeylSpinor.left.tprod WeylSpinor.left).tprod
      (WeylSpinor.right.tprod WeylSpinor.right)) where
  toLinearEquiv := TensorProduct.comm ℂ _ _
  isIntertwining' g := by ext x y; rfl

def spinContraction := WeylSpinor.four.comp spinSwap.toIntertwiningMap
def spinWitness := (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ]
  (weakBasis 0 ⊗ₜ[ℂ] weakBasis 1)

theorem spin_unique (f : IntertwiningMap spin (Representation.trivial ℂ WeylSpinor.Group ℂ)) :
    f = f spinWitness • spinContraction := by
  have h := WeylSpinorUniqueness.eq_smul_four (f.comp spinSwap.symm.toIntertwiningMap)
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  have hv := DFunLike.congr_fun h (spinSwap v)
  change f (spinSwap.toLinearEquiv.symm (spinSwap.toLinearEquiv v)) =
    f spinWitness * spinContraction v at hv
  change f v = f spinWitness * spinContraction v
  simpa only [LinearEquiv.symm_apply_apply] using hv

def localRepresentation := external duqlRepresentation spin
def localContraction := coefficient duqlIntertwiner spinContraction
def localWitness := duqlWitness ⊗ₜ[ℂ] spinWitness

theorem local_normalized : localContraction localWitness = 1 := by
  change duql duqlWitness * spinContraction spinWitness = 1
  rw [duql_witness]
  norm_num [localContraction, localWitness, spinContraction, spinSwap, spinWitness,
    duqlIntertwiner, WeylSpinor.four, WeylSpinor.epsilonLeft, WeylSpinor.epsilonRight,
    eps2, weakBasis]

theorem local_unique (f : IntertwiningMap localRepresentation
    (Representation.trivial ℂ (GaugeGroup × WeylSpinor.Group) ℂ)) :
    f = f localWitness • localContraction :=
  NormalizedInvariantFactor.product_unique _ _ _ _ _ _ DuqlGaugeUniqueness.unique spin_unique f

def downSpin := external downRight WeylSpinor.right
def upSpin := external upRight WeylSpinor.right
def quarkSpin := external quark WeylSpinor.left
def leptonSpin := external lepton WeylSpinor.left

def localRegroup : Representation.Equiv
    ((downSpin.tprod upSpin).tprod (quarkSpin.tprod leptonSpin)) localRepresentation :=
  regroupFour downRight upRight quark lepton
    WeylSpinor.right WeylSpinor.right WeylSpinor.left WeylSpinor.left

variable {R D U Q L : Type*} [Group R]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup L] [Module ℂ L]
  (d : Representation ℂ R D) (u : Representation ℂ R U)
  (q : Representation ℂ R Q) (l : Representation ℂ R L)

def flavor := (d.tprod u).tprod (q.tprod l)
def fields := ((external downSpin d).tprod (external upSpin u)).tprod
  ((external quarkSpin q).tprod (external leptonSpin l))

abbrev Coefficient := IntertwiningMap (fields d u q l)
  (Representation.trivial ℂ ((GaugeGroup × WeylSpinor.Group) × R) ℂ)
abbrev Residual := IntertwiningMap (flavor d u q l) (Representation.trivial ℂ R ℂ)

def regroup : Representation.Equiv (fields d u q l)
    (external localRepresentation (flavor d u q l)) :=
  (regroupFour downSpin upSpin quarkSpin leptonSpin d u q l).trans
    (externalEquiv localRegroup (Representation.Equiv.refl _))

/-- Both inverse identities are part of this equivalence; no finite dimension is needed. -/
def homEquiv : Coefficient d u q l ≃ₗ[ℂ] Residual d u q l :=
  (InvariantCoefficientTransport.alongEquiv (regroup d u q l)).trans
    (NormalizedInvariantFactor.equiv localRepresentation (flavor d u q l)
      localContraction localWitness local_normalized local_unique)

theorem exists_nonzero_iff : (∃ f : Coefficient d u q l, f ≠ 0) ↔
    ∃ k : Residual d u q l, k ≠ 0 := by
  let e := homEquiv d u q l
  constructor
  · rintro ⟨f,hf⟩
    exact ⟨e f, fun h => hf (e.injective (h.trans e.map_zero.symm))⟩
  · rintro ⟨k,hk⟩
    exact ⟨e.symm k, fun h => hk (e.symm.injective (h.trans e.symm.map_zero.symm))⟩

end
end Physics.DuqlOrderedCompleteness
