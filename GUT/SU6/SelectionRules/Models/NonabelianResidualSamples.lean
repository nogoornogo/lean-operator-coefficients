import GUT.SU6.SelectionRules.Models.StandardSMUVFields
import Physics.StandardModel.Operators.BaryonOne.Qque.NonabelianQqueSamples

open Physics

/-! Explicit non-Abelian flavor factors on the actual 15 + 2 bar6 carrier.
Restriction is certified; no mass or VEV realization is claimed. -/
namespace GUT.SU6NonabelianResidualSamples
set_option autoImplicit false
noncomputable section
open Math Representation ExternalInvariantTensor
open scoped TensorProduct
variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
  (a : Representation ℂ H V)

def ambient := external StandardSMUVFields.uvRho a
def restriction : StandardSMGaugeTensor.GaugeGroup × H →*
    ActualRestriction.SU6 × H :=
  StandardSMGroup.hom.prodMap (MonoidHom.id H)

theorem restricted_action : (ambient a).comp (restriction (H := H)) =
    external (StandardSMUVFields.uvRho.comp StandardSMGroup.hom) a := by
  apply MonoidHom.ext
  intro g
  apply TensorProduct.ext'
  intro x y
  rfl

def branching : Representation.Equiv ((ambient a).comp (restriction (H := H)))
    (external StandardSMUVFields.decomposed a) := by
  rw [restricted_action]
  exact externalEquiv StandardSMUVFields.gaugeEquiv (Representation.Equiv.refl a)

def s3Ambient := ambient S3DipoleSelection.action
def a4Ambient := ambient FiniteFlavorControls.a4
def s3Branching := branching S3DipoleSelection.action
def a4Branching := branching FiniteFlavorControls.a4

theorem s3_dimension : Module.finrank ℂ
    (StandardSMUVFields.UV ⊗[ℂ] S3DipoleSelection.V) = 81 := by
  rw [Module.finrank_tensorProduct, StandardSMUVFields.uv_finrank]
  norm_num [S3DipoleSelection.V]

theorem a4_dimension : Module.finrank ℂ
    (StandardSMUVFields.UV ⊗[ℂ] FiniteFlavorControls.SumZero 4) = 81 := by
  rw [Module.finrank_tensorProduct, StandardSMUVFields.uv_finrank,
    FiniteFlavorControls.a4_dimension]

end
end GUT.SU6NonabelianResidualSamples
