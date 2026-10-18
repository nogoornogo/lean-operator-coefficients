import Physics.StandardModel.Gauge.DuueGaugeUniqueness
import Physics.FieldTheory.Spinor.FourSameWeylCompleteness
import Math.RepresentationTheory.InvariantCoefficientTransport

open Math

/-! Ordered duue coefficients, before the repeated-up exchange constraint. -/
namespace GUT.DuueOrderedCompleteness
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor StandardSMGaugeTensor
open scoped TensorProduct

def localRepresentation := external DuueGaugeUniqueness.representation
  (FourSameWeylCompleteness.representation true)
def localPairing (i : Fin 2) := coefficient DuueGaugeUniqueness.intertwiner
  (FourSameWeylCompleteness.basisPairing true i)
def localProbe (i : Fin 2) := DuueGaugeUniqueness.witness ⊗ₜ[ℂ] FourSameWeylCompleteness.probe i

theorem localPairing_probe (i j : Fin 2) : localPairing i (localProbe j) = if i = j then 1 else 0 := by
  change DuueGaugeUniqueness.intertwiner DuueGaugeUniqueness.witness *
    FourSameWeylCompleteness.basisPairing true i (FourSameWeylCompleteness.probe j) = _
  rw [DuueGaugeUniqueness.normalized, one_mul, FourSameWeylCompleteness.basisPairing_probe]

theorem local_formula (f : IntertwiningMap localRepresentation
    (Representation.trivial ℂ (GaugeGroup × WeylSpinor.Group) ℂ)) :
    f = ∑ i, f (localProbe i) • localPairing i :=
  FiniteInvariantFactor.product_left_line _ _ _ _ DuueGaugeUniqueness.unique
    _ _ (FourSameWeylCompleteness.basisPairing_formula true) f

def upSpin := external upRight WeylSpinor.right
def downSpin := external downRight WeylSpinor.right
def electronSpin := external electronRight WeylSpinor.right

def localRegroup : Representation.Equiv
    ((upSpin.tprod upSpin).tprod (downSpin.tprod electronSpin)) localRepresentation :=
  regroupFour upRight upRight downRight electronRight
    WeylSpinor.right WeylSpinor.right WeylSpinor.right WeylSpinor.right

variable {R U D E : Type*} [Group R]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup D] [Module ℂ D]
  [AddCommGroup E] [Module ℂ E]
  (u : Representation ℂ R U) (d : Representation ℂ R D) (e : Representation ℂ R E)

def flavor := (u.tprod u).tprod (d.tprod e)
def fields := ((external upSpin u).tprod (external upSpin u)).tprod
  ((external downSpin d).tprod (external electronSpin e))
abbrev Coefficient := IntertwiningMap (fields u d e)
  (Representation.trivial ℂ ((GaugeGroup × WeylSpinor.Group) × R) ℂ)
abbrev Residual := IntertwiningMap (flavor u d e) (Representation.trivial ℂ R ℂ)

def regroup : Representation.Equiv (fields u d e)
    (external localRepresentation (flavor u d e)) :=
  (regroupFour upSpin upSpin downSpin electronSpin u u d e).trans
    (externalEquiv localRegroup (Representation.Equiv.refl _))

def homEquiv : Coefficient u d e ≃ₗ[ℂ] (Fin 2 → Residual u d e) :=
  (InvariantCoefficientTransport.alongEquiv (regroup u d e)).trans
    (FiniteInvariantFactor.equiv localRepresentation (flavor u d e)
      localPairing localProbe localPairing_probe local_formula)

theorem assemble_apply (k : Fin 2 → Residual u d e)
    (a b c : SMEpsilonTensor.Color) (z : ℂ) (s t v w : WeylSpinor.Space)
    (x y : U) (h : D) (j : E) :
    (homEquiv u d e).symm k
      ((((a ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] ((b ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
        (((c ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] h) ⊗ₜ[ℂ] ((z ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] j))) =
      SMEpsilonTensor.eps3 a b c * z *
        (FourDoubletInvariant.eps s t * FourDoubletInvariant.eps v w *
          k 0 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j)) +
        FourDoubletInvariant.eps s v * FourDoubletInvariant.eps t w *
          k 1 ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))) := by
  change FiniteInvariantFactor.assemble localRepresentation (flavor u d e) localPairing k
    ((((a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] z)) ⊗ₜ[ℂ]
      ((s ⊗ₜ[ℂ] t) ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w))) ⊗ₜ[ℂ]
      ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] j))) = _
  simp [FiniteInvariantFactor.assemble, Fin.sum_univ_two, localPairing, coefficient,
    FourSameWeylCompleteness.basisPairing, FourSameWeylCompleteness.pairing,
    FourDoubletInvariant.tensorPairing_apply, DuueGaugeUniqueness.intertwiner]
  ring

end
end GUT.DuueOrderedCompleteness
