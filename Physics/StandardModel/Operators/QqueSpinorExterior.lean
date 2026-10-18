import Physics.FieldTheory.Spinor.WeylSpinor
import Physics.StandardModel.Gauge.ExplicitSMResidualTensor
import Math.RepresentationTheory.SymmetricInvariantPairing
import Math.RepresentationTheory.FourSlotAlternation

open Math

namespace GUT.QqueSpinorExterior
set_option autoImplicit false
noncomputable section
open Representation ExternalInvariantTensor SplitRepresentationProjection SMEpsilonTensor
open scoped TensorProduct

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance

section Spin
variable {K Q U E : Type*} [Group K]
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ K Q) (u : Representation ℂ K U) (e : Representation ℂ K E)

abbrev qSpin := external q WeylSpinor.left
abbrev uSpin := external u WeylSpinor.right
abbrev eSpin := external e WeylSpinor.right

def ordered
    (f : IntertwiningMap ((q.tprod q).tprod (u.tprod e)) (Representation.trivial ℂ K ℂ)) :
    IntertwiningMap (((qSpin q).tprod (qSpin q)).tprod ((uSpin u).tprod (eSpin e)))
      (Representation.trivial ℂ (K × WeylSpinor.Group) ℂ) :=
  (coefficient f WeylSpinor.four).comp
    (regroupFour q q u e WeylSpinor.left WeylSpinor.left
      WeylSpinor.right WeylSpinor.right).toIntertwiningMap

@[simp] theorem ordered_apply
    (f : IntertwiningMap ((q.tprod q).tprod (u.tprod e)) (Representation.trivial ℂ K ℂ))
    (x y : Q) (z : U) (w : E) (s t v l : WeylSpinor.Space) :
    ordered q u e f (((x ⊗ₜ[ℂ] s) ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] t)) ⊗ₜ[ℂ]
      ((z ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] l))) =
      f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) * (eps2 s t * eps2 v l) := rfl

abbrev fullAction := FourSlotAlternation.action (qSpin q) (uSpin u) (eSpin e)

abbrev OrderedCoefficient :=
  IntertwiningMap (((qSpin q).tprod (qSpin q)).tprod ((uSpin u).tprod (eSpin e)))
    (Representation.trivial ℂ (K × WeylSpinor.Group) ℂ)

abbrev ExteriorCoefficient :=
  IntertwiningMap ((fullAction q u e).exteriorPower 4)
    (Representation.trivial ℂ (K × WeylSpinor.Group) ℂ)

def HasNonzeroAlternation : Prop :=
  ∃ f : OrderedCoefficient q u e,
    FourSlotAlternation.coefficient (qSpin q) (uSpin u) (eSpin e) f ≠ 0

theorem HasNonzeroAlternation.exists_exterior (h : HasNonzeroAlternation q u e) :
    ∃ f : ExteriorCoefficient q u e, f ≠ 0 := by
  obtain ⟨f, hf⟩ := h
  exact ⟨FourSlotAlternation.coefficient _ _ _ f, hf⟩

def exterior
    (f : IntertwiningMap ((q.tprod q).tprod (u.tprod e)) (Representation.trivial ℂ K ℂ)) :=
  FourSlotAlternation.coefficient (qSpin q) (uSpin u) (eSpin e) (ordered q u e f)

end Spin

section Matched
variable {H A B D R : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D] [AddCommGroup R] [Module ℂ R]
  {a : Representation ℂ H A} {b : Representation ℂ H B}
  {d : Representation ℂ H D} {r : Representation ℂ H R}
  (sa : Split a r) (sb : Split b r) (sd : Split d r)

local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A) := inferInstance
-- Cache existing instances before elaborating the nested gauge/flavor/spinor tensors.
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (Color ⊗[ℂ] Module.Dual ℂ B ⊗[ℂ] WeylSpinor.Space) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] Module.Dual ℂ D ⊗[ℂ] WeylSpinor.Space) := inferInstance

abbrev qField := external StandardSMGaugeTensor.quark a
abbrev uField := external StandardSMGaugeTensor.upRight b.dual
abbrev eField := external StandardSMGaugeTensor.electronRight d.dual

def internal : IntertwiningMap
    (((qField (a := a)).tprod (qField (a := a))).tprod
      ((uField (b := b)).tprod (eField (d := d))))
    (Representation.trivial ℂ (StandardSMGaugeTensor.GaugeGroup × H) ℂ) :=
  ExplicitSMResidualTensor.qque a a b.dual d.dual
    (SymmetricInvariantPairing.coefficient sa sb sd)

def matched : IntertwiningMap
    ((fullAction (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] A)
      (U := Color ⊗[ℂ] Module.Dual ℂ B) (E := ℂ ⊗[ℂ] Module.Dual ℂ D)
      (qField (a := a)) (uField (b := b)) (eField (d := d))).exteriorPower
      (M := (StandardSMGaugeTensor.Quark ⊗[ℂ] A ⊗[ℂ] WeylSpinor.Space) ×
        (Color ⊗[ℂ] Module.Dual ℂ B ⊗[ℂ] WeylSpinor.Space) ×
        (ℂ ⊗[ℂ] Module.Dual ℂ D ⊗[ℂ] WeylSpinor.Space)) 4)
    (Representation.trivial ℂ
      ((StandardSMGaugeTensor.GaugeGroup × H) × WeylSpinor.Group) ℂ) :=
  exterior (qField (a := a)) (uField (b := b)) (eField (d := d)) (internal sa sb sd)

theorem matched_diagonal (x : R) (phi : Module.Dual ℂ R) (hphi : phi x = 1) :
    matched sa sb sd (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots
      (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] sa.embed x) ⊗ₜ[ℂ] weakBasis 0)
      (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] sa.embed x) ⊗ₜ[ℂ] weakBasis 1)
      ((colorBasis 2 ⊗ₜ[ℂ] sb.dual.embed phi) ⊗ₜ[ℂ] weakBasis 0)
      (((1 : ℂ) ⊗ₜ[ℂ] sd.dual.embed phi) ⊗ₜ[ℂ] weakBasis 1))) = 4 := by
  rw [matched, exterior, FourSlotAlternation.coefficient_slots]
  simp only [ordered_apply, internal, ExplicitSMResidualTensor.qque_tmul,
    StandardSMGaugeTensor.qque_tmul, SymmetricInvariantPairing.diagonal sa sb sd x phi hphi]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]

theorem matched_nonzero [Nontrivial R] : matched sa sb sd ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : R)
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  intro hz
  have hv := matched_diagonal sa sb sd x phi hphi
  rw [hz] at hv
  norm_num at hv

/-- A named endpoint avoids repeatedly elaborating the full exterior tensor
on concrete, source-dependent multiplicity carriers. -/
def HasModelExterior : Prop :=
  ∃ f : ExteriorCoefficient
    (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] A)
    (U := Color ⊗[ℂ] Module.Dual ℂ B) (E := ℂ ⊗[ℂ] Module.Dual ℂ D)
    (qField (a := a)) (uField (b := b)) (eField (d := d)), f ≠ 0

include sa sb sd in
theorem hasModelExterior [Nontrivial R] : HasModelExterior (a := a) (b := b) (d := d) :=
  ⟨matched sa sb sd, matched_nonzero sa sb sd⟩

include sa sb sd in
set_option maxHeartbeats 200000 in
theorem exists_on_fields [Nontrivial R]
    {Q U E : Type*} [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup E] [Module ℂ E]
    (q : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) Q)
    (u : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) U)
    (e : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) E)
    (eqQ : Representation.Equiv q (qField (a := a)))
    (eqU : Representation.Equiv u (uField (b := b)))
    (eqE : Representation.Equiv e (eField (d := d))) :
    HasNonzeroAlternation q u e := by
  let eQ := externalEquiv eqQ (Representation.Equiv.refl WeylSpinor.left)
  let eU := externalEquiv eqU (Representation.Equiv.refl WeylSpinor.right)
  let eE := externalEquiv eqE (Representation.Equiv.refl WeylSpinor.right)
  let f := ordered (qField (a := a)) (uField (b := b)) (eField (d := d))
    (internal sa sb sd)
  refine ⟨f.comp (tensorEquiv (tensorEquiv eQ eQ)
    (tensorEquiv eU eE)).toIntertwiningMap, ?_⟩
  exact FourSlotAlternation.coefficient_transport_ne_zero
    (A' := StandardSMGaugeTensor.Quark ⊗[ℂ] A ⊗[ℂ] WeylSpinor.Space)
    (B' := Color ⊗[ℂ] Module.Dual ℂ B ⊗[ℂ] WeylSpinor.Space)
    (C' := ℂ ⊗[ℂ] Module.Dual ℂ D ⊗[ℂ] WeylSpinor.Space)
    (a' := qSpin (qField (a := a))) (b' := uSpin (uField (b := b)))
    (c' := eSpin (eField (d := d)))
    (qSpin q) (uSpin u) (eSpin e) eQ eU eE f (matched_nonzero sa sb sd)

end Matched
end
end GUT.QqueSpinorExterior
