import Physics.StandardModel.Operators.S3DipoleSelection
import Physics.StandardModel.Operators.QqueSpinorExterior
import Math.RepresentationTheory.FiniteFlavorControls
import Math.RepresentationTheory.Decomposition.ExternalTensorDual

/-! Concrete non-Abelian common-flavor tests on actual physical exterior
coefficients. These do not supply a mass radical or a quantum symmetry. -/
namespace GUT.NonabelianQqueSamples
set_option autoImplicit false
noncomputable section
open Math Representation SplitRepresentationProjection
open scoped TensorProduct
local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance

/-- Use the actual duals of left-handed uc/ec species, not independent
right-handed flavor assignments. No Abelian or irreducible hypothesis. -/
theorem common_flavor_left_species {H V : Type} [Group H]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (a : Representation ℂ H V) :
    QqueSpinorExterior.HasNonzeroAlternation
      (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] V)
      (ExternalInvariantTensor.external StandardSMGaugeTensor.quark a)
      (ExternalInvariantTensor.external StandardSMGaugeTensor.upRight.dual a).dual
      (ExternalInvariantTensor.external StandardSMGaugeTensor.electronRight.dual a).dual := by
  let s := Split.ofEquiv (Representation.Equiv.refl a)
  exact QqueSpinorExterior.exists_on_fields s s s _ _ _
    (Representation.Equiv.refl _)
    (ExternalTensorDual.rightModelEquiv StandardSMGaugeTensor.upRight a)
    (ExternalTensorDual.rightModelEquiv StandardSMGaugeTensor.electronRight a)

theorem s3_left_species_allowed :
    QqueSpinorExterior.HasNonzeroAlternation
      (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] S3DipoleSelection.V)
      (ExternalInvariantTensor.external StandardSMGaugeTensor.quark S3DipoleSelection.action)
      (ExternalInvariantTensor.external StandardSMGaugeTensor.upRight.dual S3DipoleSelection.action).dual
      (ExternalInvariantTensor.external StandardSMGaugeTensor.electronRight.dual S3DipoleSelection.action).dual :=
  common_flavor_left_species S3DipoleSelection.action

theorem a4_left_species_allowed :
    QqueSpinorExterior.HasNonzeroAlternation
      (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] FiniteFlavorControls.SumZero 4)
      (ExternalInvariantTensor.external StandardSMGaugeTensor.quark FiniteFlavorControls.a4)
      (ExternalInvariantTensor.external StandardSMGaugeTensor.upRight.dual FiniteFlavorControls.a4).dual
      (ExternalInvariantTensor.external StandardSMGaugeTensor.electronRight.dual FiniteFlavorControls.a4).dual :=
  common_flavor_left_species FiniteFlavorControls.a4

theorem s3_qque_allowed : QqueSpinorExterior.HasModelExterior
    (a := S3DipoleSelection.action) (b := S3DipoleSelection.action)
    (d := S3DipoleSelection.action) :=
  QqueSpinorExterior.hasModelExterior
    (Split.ofEquiv (Representation.Equiv.refl S3DipoleSelection.action))
    (Split.ofEquiv (Representation.Equiv.refl S3DipoleSelection.action))
    (Split.ofEquiv (Representation.Equiv.refl S3DipoleSelection.action))

theorem a4_qque_allowed : QqueSpinorExterior.HasModelExterior
    (a := FiniteFlavorControls.a4) (b := FiniteFlavorControls.a4)
    (d := FiniteFlavorControls.a4) :=
  QqueSpinorExterior.hasModelExterior
    (Split.ofEquiv (Representation.Equiv.refl FiniteFlavorControls.a4))
    (Split.ofEquiv (Representation.Equiv.refl FiniteFlavorControls.a4))
    (Split.ofEquiv (Representation.Equiv.refl FiniteFlavorControls.a4))

/-- The representation, not just the abstract group, is noncommutative. -/
theorem s3_action_noncommuting :
    ¬ Commute (S3DipoleSelection.action (Equiv.swap 0 1))
      (S3DipoleSelection.action (Equiv.swap 1 2)) := by
  intro h
  have he := congrArg (fun f : Module.End ℂ S3DipoleSelection.V =>
    f (Pi.single 0 1) 1) h.eq
  norm_num [Module.End.mul_apply, S3DipoleSelection.action_apply,
    Equiv.swap_apply_def, Pi.single_apply] at he

theorem a4_action_noncommuting :
    ¬ Commute (FiniteFlavorControls.a4 FiniteFlavorControls.a4Flip1)
      (FiniteFlavorControls.a4 FiniteFlavorControls.a4Cycle) := by
  intro h
  have he := congrArg (fun f : Module.End ℂ (FiniteFlavorControls.SumZero 4) =>
    (f (FiniteFlavorControls.difference 1 0)).val 0) h.eq
  change (FiniteFlavorControls.difference 1 0).val
    ((FiniteFlavorControls.a4Cycle.val)⁻¹ ((FiniteFlavorControls.a4Flip1.val)⁻¹ 0)) =
    (FiniteFlavorControls.difference 1 0).val
    ((FiniteFlavorControls.a4Flip1.val)⁻¹ ((FiniteFlavorControls.a4Cycle.val)⁻¹ 0)) at he
  norm_num [FiniteFlavorControls.a4Flip1, FiniteFlavorControls.a4Cycle,
    FiniteFlavorControls.difference, Equiv.swap_apply_def, Pi.single_apply] at he

/-- A three-dimensional factor with no invariant functional still allows
the actual qque four-field exterior coefficient. -/
theorem a4_no_single_invariant_but_qque :
    (∀ f : IntertwiningMap FiniteFlavorControls.a4
      (Representation.trivial ℂ FiniteFlavorControls.A4 ℂ), f = 0) ∧
    QqueSpinorExterior.HasModelExterior (a := FiniteFlavorControls.a4)
      (b := FiniteFlavorControls.a4) (d := FiniteFlavorControls.a4) :=
  ⟨FiniteFlavorControls.a4_no_invariant_functional, a4_qque_allowed⟩

end
end GUT.NonabelianQqueSamples
