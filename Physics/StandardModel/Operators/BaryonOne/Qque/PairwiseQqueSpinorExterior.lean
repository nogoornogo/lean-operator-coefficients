import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorExterior
import Math.RepresentationTheory.Tensors.PairwiseInvariantPairing

open Math

/-! Qque alternation from Q/up and Q/e split quotients, which may differ.
The common Q vector witnesses nonzero descent without cross-projection rules. -/

namespace Physics.PairwiseQqueSpinorExterior
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection SMEpsilonTensor
open QqueSpinorExterior
open scoped TensorProduct

variable {H A B D R S : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]
  [AddCommGroup S] [Module ℂ S]
  {a : Representation ℂ H A} {b : Representation ℂ H B}
  {d : Representation ℂ H D} {r : Representation ℂ H R} {s : Representation ℂ H S}
  (ar : Split a r) (br : Split b r) (as' : Split a s) (ds : Split d s)

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A) := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (Color ⊗[ℂ] Module.Dual ℂ B ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] Module.Dual ℂ D ⊗[ℂ] WeylSpinor.Space) := inferInstance

def internal : IntertwiningMap
    (((qField (a := a)).tprod (qField (a := a))).tprod
      ((uField (b := b)).tprod (eField (d := d))))
    (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) ℂ) :=
  ExplicitSMResidualTensor.qque a a b.dual d.dual
    (PairwiseInvariantPairing.coefficient ar br as' ds)

def matched : ExteriorCoefficient
    (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] A)
    (U := Color ⊗[ℂ] Module.Dual ℂ B) (E := ℂ ⊗[ℂ] Module.Dual ℂ D)
    (qField (a := a)) (uField (b := b)) (eField (d := d)) :=
  exterior (qField (a := a)) (uField (b := b)) (eField (d := d)) (internal ar br as' ds)

theorem matched_diagonal (x : A) (phi : Module.Dual ℂ R) (psi : Module.Dual ℂ S)
    (hp : phi (ar.project x) = 1) (hq : psi (as'.project x) = 1) :
    matched ar br as' ds (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
      (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] weakBasis 0)
      (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] weakBasis 1)
      ((colorBasis 2 ⊗ₜ[ℂ] br.dual.embed phi) ⊗ₜ[ℂ] weakBasis 0)
      (((1 : ℂ) ⊗ₜ[ℂ] ds.dual.embed psi) ⊗ₜ[ℂ] weakBasis 1))) = 4 := by
  rw [matched, exterior, FourSlotAlternation.coefficient_slots]
  simp only [ordered_apply, internal, ExplicitSMResidualTensor.qque_tmul,
    StandardSMGaugeTensor.qque_tmul, PairwiseInvariantPairing.diagonal ar br as' ds x phi psi hp hq]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]

theorem matched_nonzero [Nontrivial R] [Nontrivial S] : matched ar br as' ds ≠ 0 := by
  obtain ⟨x, phi, psi, hp, hq⟩ := PairwiseInvariantPairing.exists_diagonal ar as'
  intro hz
  have he := matched_diagonal ar br as' ds x phi psi hp hq
  rw [hz] at he
  norm_num at he

include ar br as' ds in
theorem exists_on_fields [Nontrivial R] [Nontrivial S]
    {Q U E : Type*} [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup E] [Module ℂ E]
    (q : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) Q)
    (u : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) U)
    (e : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) E)
    (eqQ : Representation.Equiv q (qField (a := a)))
    (eqU : Representation.Equiv u (uField (b := b)))
    (eqE : Representation.Equiv e (eField (d := d))) : HasNonzeroAlternation q u e := by
  let eQ := externalEquiv eqQ (Representation.Equiv.refl WeylSpinor.left)
  let eU := externalEquiv eqU (Representation.Equiv.refl WeylSpinor.right)
  let eE := externalEquiv eqE (Representation.Equiv.refl WeylSpinor.right)
  let f := ordered (qField (a := a)) (uField (b := b)) (eField (d := d))
    (internal ar br as' ds)
  refine ⟨f.comp (tensorEquiv (tensorEquiv eQ eQ)
    (tensorEquiv eU eE)).toIntertwiningMap, ?_⟩
  exact FourSlotAlternation.coefficient_transport_ne_zero
    (A' := StandardSMGaugeTensor.Quark ⊗[ℂ] A ⊗[ℂ] WeylSpinor.Space)
    (B' := Color ⊗[ℂ] Module.Dual ℂ B ⊗[ℂ] WeylSpinor.Space)
    (C' := ℂ ⊗[ℂ] Module.Dual ℂ D ⊗[ℂ] WeylSpinor.Space)
    (a' := qSpin (qField (a := a))) (b' := uSpin (uField (b := b)))
    (c' := eSpin (eField (d := d)))
    (qSpin q) (uSpin u) (eSpin e) eQ eU eE f (matched_nonzero ar br as' ds)

end
end Physics.PairwiseQqueSpinorExterior
