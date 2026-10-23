import Physics.StandardModel.Gauge.Tensors.StandardSMGaugeTensor
import Math.RepresentationTheory.Tensors.ExternalInvariantTensor

open Math

/-! Ordered SM x H tensors with explicit gauge/multiplicity decomposition.
This does not infer a full-SM extension from torus data. -/

namespace Physics.ExplicitSMResidualTensor
set_option autoImplicit false
noncomputable section

open Representation ExternalInvariantTensor
open scoped TensorProduct
open StandardSMGaugeTensor

variable {H A B C D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B)
  (c : Representation ℂ H C) (d : Representation ℂ H D)

abbrev multiplicity := (a.tprod b).tprod (c.tprod d)

abbrev fields := ((external quark a).tprod (external quark b)).tprod
  ((external upRight c).tprod (external electronRight d))

def qque (f : IntertwiningMap (multiplicity a b c d) (Representation.trivial ℂ H ℂ)) :
    IntertwiningMap (fields a b c d) (Representation.trivial ℂ (GaugeGroup × H) ℂ) :=
  (coefficient qqueIntertwiner f).comp
    (regroupFour quark quark upRight electronRight a b c d).toIntertwiningMap

theorem qque_ne_zero
    (f : IntertwiningMap (multiplicity a b c d) (Representation.trivial ℂ H ℂ))
    (hf : f ≠ 0) : qque a b c d f ≠ 0 := by
  have hg : qqueIntertwiner ≠ 0 := by
    intro he
    have hz := DFunLike.congr_fun he qqueWitness
    exact one_ne_zero (StandardSMGaugeTensor.qque_witness.symm.trans hz)
  exact comp_equiv_ne_zero _
    (coefficient_ne_zero qqueIntertwiner f hg hf) _

/-- Gauge and multiplicity factors are interleaved in physical field order. -/
theorem qque_tmul
    (f : IntertwiningMap (multiplicity a b c d) (Representation.trivial ℂ H ℂ))
    (q₁ q₂ : Quark) (u : SMEpsilonTensor.Color) (e : ℂ)
    (x : A) (y : B) (z : C) (w : D) :
    qque a b c d f (((q₁ ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (q₂ ⊗ₜ[ℂ] y)) ⊗ₜ[ℂ]
      ((u ⊗ₜ[ℂ] z) ⊗ₜ[ℂ] (e ⊗ₜ[ℂ] w))) =
      StandardSMGaugeTensor.qque ((q₁ ⊗ₜ[ℂ] q₂) ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] e)) *
        f ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w)) := by
  rfl

@[simp] theorem qque_zero : qque a b c d 0 = 0 := by
  ext q₁ x q₂ y u z e w
  change _ * (0 : ℂ) = 0
  exact mul_zero _

theorem qque_ne_zero_iff
    (f : IntertwiningMap (multiplicity a b c d) (Representation.trivial ℂ H ℂ)) :
    qque a b c d f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · intro h hf
    subst f
    exact h (qque_zero a b c d)
  · exact qque_ne_zero a b c d f

variable {Q U E : Type*}
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ (GaugeGroup × H) Q)
  (u : Representation ℂ (GaugeGroup × H) U)
  (e : Representation ℂ (GaugeGroup × H) E)

/-- Both Q slots are the same actual field; two coordinate presentations can
identify their multiplicities with different monitored weight spaces. -/
theorem exists_on_fields
    (eq₁ : Representation.Equiv q (external quark a))
    (eq₂ : Representation.Equiv q (external quark b))
    (eu : Representation.Equiv u (external upRight c))
    (ee : Representation.Equiv e (external electronRight d))
    (f : IntertwiningMap (multiplicity a b c d) (Representation.trivial ℂ H ℂ))
    (hf : f ≠ 0) :
    ∃ p : IntertwiningMap ((q.tprod q).tprod (u.tprod e))
      (Representation.trivial ℂ (GaugeGroup × H) ℂ), p ≠ 0 := by
  let s := tensorEquiv (tensorEquiv eq₁ eq₂) (tensorEquiv eu ee)
  exact ⟨(qque a b c d f).comp s.toIntertwiningMap,
    comp_equiv_ne_zero _ (qque_ne_zero a b c d f hf) s⟩

end
end Physics.ExplicitSMResidualTensor
