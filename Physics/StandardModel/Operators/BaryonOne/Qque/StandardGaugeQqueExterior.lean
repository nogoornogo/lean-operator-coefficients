import Physics.StandardModel.Operators.BaryonOne.Qque.PhysicalQqueEndpoint

namespace Physics.StandardGaugeQqueExterior
set_option autoImplicit false
noncomputable section
open Math Representation StandardSMGaugeTensor SMEpsilonTensor QqueSpinorExterior
open ExternalInvariantTensor
open scoped TensorProduct
local instance : AddCommGroup Quark := inferInstance

def internal : IntertwiningMap ((quark.tprod quark).tprod (upRight.tprod electronRight))
    (Representation.trivial ℂ GaugeGroup ℂ) := qqueIntertwiner

theorem standard_nonzero : HasNonzeroAlternation quark upRight electronRight := by
  refine ⟨ordered quark upRight electronRight internal, ?_⟩
  apply FourSlotAlternation.coefficient_ne_zero
    (qSpin quark) (uSpin upRight) (eSpin electronRight)
    (ordered quark upRight electronRight internal)
    ((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] weakBasis 0)
    ((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] weakBasis 1)
    (colorBasis 2 ⊗ₜ[ℂ] weakBasis 0)
    ((1 : ℂ) ⊗ₜ[ℂ] weakBasis 1)
  simp only [ordered_apply]
  change StandardSMGaugeTensor.qque _ * _ - StandardSMGaugeTensor.qque _ * _ ≠ 0
  rw [qque_tmul, qque_tmul]
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff]

variable {Q U E : Type*}
  [AddCommGroup Q] [Module ℂ Q] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup E] [Module ℂ E]

theorem on_fields (q : Representation ℂ GaugeGroup Q)
    (u : Representation ℂ GaugeGroup U) (e : Representation ℂ GaugeGroup E)
    (eqQ : Representation.Equiv q quark) (eqU : Representation.Equiv u upRight)
    (eqE : Representation.Equiv e electronRight) : PhysicalQqueEndpoint.HasExterior q u e := by
  obtain ⟨f,hf⟩ := standard_nonzero
  let eQ := externalEquiv eqQ (Representation.Equiv.refl WeylSpinor.left)
  let eU := externalEquiv eqU (Representation.Equiv.refl WeylSpinor.right)
  let eE := externalEquiv eqE (Representation.Equiv.refl WeylSpinor.right)
  apply PhysicalQqueEndpoint.of_alternation
  refine ⟨f.comp (tensorEquiv (tensorEquiv eQ eQ) (tensorEquiv eU eE)).toIntertwiningMap, ?_⟩
  exact FourSlotAlternation.coefficient_transport_ne_zero (qSpin q) (uSpin u) (eSpin e) eQ eU eE f hf
end
end Physics.StandardGaugeQqueExterior
