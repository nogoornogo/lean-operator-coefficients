import Physics.StandardModel.Operators.BaryonOne.Qque.S3QqueTensorSamples
import Physics.FieldTheory.Fields.SelectedFields

/-! A nonabelian retained action uses the same kernel/inverse-map factory.
The positive qque functional and its exchange symmetry are transported on
the existing ordered source, without a common flavor-representation premise. -/
namespace Physics.S3FieldConnection
set_option autoImplicit false
noncomputable section
open Math Representation S3QqueTensorSamples
open scoped TensorProduct

def ambient := q.prod sign
def constraint : IntertwiningMap ambient sign := IntertwiningMap.snd ℂ q sign
def selected := SelectedFields.dirac constraint
def embed : IntertwiningMap q ambient := IntertwiningMap.inl ℂ q sign
def extract : (V × V) →ₗ[ℂ] V := LinearMap.fst ℂ V V

def dictionary : Representation.Equiv q selected.toRepresentation :=
  FieldSelection.ofMaps selected embed extract (fun _ => rfl) (fun _ => rfl)
    (by intro u hu; exact Prod.ext rfl (show u.2 = 0 from hu).symm)

def sourceEquiv := ExternalInvariantTensor.tensorEquiv
  (ExternalInvariantTensor.tensorEquiv dictionary dictionary)
  (Representation.Equiv.refl (sign.tprod sign))

def coefficient := InvariantCoefficientTransport.alongEquiv sourceEquiv positiveResidual.val

theorem coefficient_evaluation (v : (V ⊗[ℂ] V) ⊗[ℂ] (V ⊗[ℂ] V)) :
    coefficient (sourceEquiv v) = positiveResidual.val v :=
  congrArg positiveResidual.val (sourceEquiv.toLinearEquiv.symm_apply_apply v)

theorem coefficient_nonzero : coefficient ≠ 0 := by
  intro h
  have hh := coefficient_evaluation ((unit 0 ⊗ₜ[ℂ] unit 0) ⊗ₜ[ℂ] (unit 0 ⊗ₜ[ℂ] unit 0))
  rw [h] at hh
  exact zero_ne_one (hh.trans positive_witness)

theorem exchange_preserved (x y z w : V) :
    coefficient (sourceEquiv ((y ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) =
      coefficient (sourceEquiv ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] (z ⊗ₜ[ℂ] w))) := by
  rw [coefficient_evaluation, coefficient_evaluation]
  exact positiveResidual.property x y z w

theorem flavor_boundary : ∀ _e : Representation.Equiv q S3QqueTensorSamples.trivial, False :=
  no_q_trivial_equiv

end
end Physics.S3FieldConnection
