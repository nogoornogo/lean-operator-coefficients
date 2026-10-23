import Physics.StandardModel.Operators.BaryonOne.Qque.QqueCoefficientSector
import Physics.StandardModel.Operators.BaryonOne.Qque.QqueSpinorFactorization
import Physics.StandardModel.Gauge.Tensors.QqueGaugeFactorization
import Math.RepresentationTheory.Content.FourSlotSpeciesTransport

open Math

/-! Completeness of the symmetric residual Hom description of the intrinsic qque sector. -/
namespace Physics.QqueCoefficientCompleteness
set_option autoImplicit false
noncomputable section
open Representation QqueSpinorExterior QqueCoefficientAssembly SMEpsilonTensor
open scoped TensorProduct

variable {H A B D : Type*} [Group H]
  [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]
  [AddCommGroup D] [Module ℂ D]
  (a : Representation ℂ H A) (b : Representation ℂ H B) (d : Representation ℂ H D)

local instance : AddCommGroup StandardSMGaugeTensor.Quark := inferInstance
local instance : AddCommGroup (StandardSMGaugeTensor.Quark ⊗[ℂ] A) := inferInstance
local instance : AddCommGroup (Color ⊗[ℂ] Module.Dual ℂ B) := inferInstance
local instance : AddCommGroup (ℂ ⊗[ℂ] Module.Dual ℂ D) := inferInstance

abbrev Sector := QqueCoefficientSector.sector
  (Q := StandardSMGaugeTensor.Quark ⊗[ℂ] A)
  (U := Color ⊗[ℂ] Module.Dual ℂ B) (E := ℂ ⊗[ℂ] Module.Dual ℂ D)
  (qField (a := a)) (uField (b := b)) (eField (d := d))

def orderedRestriction (f : Sector a b d) := (1 / 2 : ℂ) •
  FourSlotRestrictionLift.restriction (qSpin (qField (a := a)))
    (uSpin (uField (b := b))) (eSpin (eField (d := d))) f.val

def residual (f : Sector a b d) : ResidualCoefficient a b d :=
  QqueGaugeFactorization.strip a a b.dual d.dual
    (QqueSpinorFactorization.strip _ _ _ (orderedRestriction a b d f))

theorem ordered_residual (f : Sector a b d) :
    ordered _ _ _ (ExplicitSMResidualTensor.qque a a b.dual d.dual (residual a b d f)) =
      orderedRestriction a b d f := by
  unfold residual
  rw [QqueGaugeFactorization.reconstruct, QqueSpinorFactorization.reconstruct]

theorem residual_symmetric (f : Sector a b d) : Symmetric a b d (residual a b d f) := by
  intro x y u e
  let v0 := (((colorBasis 0 ⊗ₜ[ℂ] weakBasis 0) ⊗ₜ[ℂ] x) ⊗ₜ[ℂ] weakBasis 0)
  let v1 := (((colorBasis 1 ⊗ₜ[ℂ] weakBasis 1) ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] weakBasis 1)
  let vu := ((colorBasis 2 ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] weakBasis 0)
  let ve := (((1 : ℂ) ⊗ₜ[ℂ] e) ⊗ₜ[ℂ] weakBasis 1)
  have hs : orderedRestriction a b d f ((v1 ⊗ₜ[ℂ] v0) ⊗ₜ[ℂ] (vu ⊗ₜ[ℂ] ve)) =
      -orderedRestriction a b d f ((v0 ⊗ₜ[ℂ] v1) ⊗ₜ[ℂ] (vu ⊗ₜ[ℂ] ve)) := by
    change (1 / 2 : ℂ) * f.val (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots v1 v0 vu ve)) =
      -((1 / 2 : ℂ) * f.val (exteriorPower.ιMulti ℂ 4 (FourSlotAlternation.slots v0 v1 vu ve)))
    rw [FourSlotRestrictionLift.restriction_swap]
    ring
  rw [← ordered_residual a b d f] at hs
  dsimp [v0, v1, vu, ve] at hs
  simp only [ExplicitSMResidualTensor.qque_tmul, StandardSMGaugeTensor.qque_tmul] at hs
  norm_num [eps2, eps3, colorBasis, weakBasis, Pi.single_apply, Fin.ext_iff] at hs
  exact hs

theorem reconstruct (f : Sector a b d) : assemble a b d (residual a b d f) = f.val := by
  unfold assemble exterior
  rw [ordered_residual]
  exact FourSlotRestrictionLift.reconstruct _ _ _ f.val f.property

variable [FiniteDimensional ℂ B] [FiniteDimensional ℂ D]

theorem fromHom_surjective : Function.Surjective (QqueCoefficientSector.fromHom a b d) := by
  intro f
  let r : symmetricCoefficients a b d := ⟨residual a b d f, residual_symmetric a b d f⟩
  refine ⟨QqueResidualHom.equiv a b d r, ?_⟩
  apply Subtype.ext
  change assemble a b d (((QqueResidualHom.equiv a b d).symm
    (QqueResidualHom.equiv a b d r)).val) = f.val
  rw [LinearEquiv.symm_apply_apply]
  exact reconstruct a b d f

def equiv : IntertwiningMap (a.symmetricPower 2) (b.tprod d) ≃ₗ[ℂ] Sector a b d :=
  LinearEquiv.ofBijective (QqueCoefficientSector.fromHom a b d)
    ⟨QqueCoefficientSector.fromHom_injective a b d, fromHom_surjective a b d⟩

variable {Q U E : Type*} [AddCommGroup Q] [Module ℂ Q]
  [AddCommGroup U] [Module ℂ U] [AddCommGroup E] [Module ℂ E]
  (q : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) Q)
  (u : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) U)
  (e : Representation ℂ (StandardSMGaugeTensor.GaugeGroup × H) E)
  (eqQ : Representation.Equiv q (qField (a := a)))
  (eqU : Representation.Equiv u (uField (b := b)))
  (eqE : Representation.Equiv e (eField (d := d)))

/-- The actual sector is still independently specified by species scaling.
Only the field identifications, not a coefficient or its existence, are supplied. -/
def onFieldsEquiv : IntertwiningMap (a.symmetricPower 2) (b.tprod d) ≃ₗ[ℂ]
    QqueCoefficientSector.sector q u e :=
  (equiv a b d).trans (FourSlotSpeciesTransport.equiv
    (ExternalInvariantTensor.externalEquiv eqQ (Representation.Equiv.refl WeylSpinor.left))
    (ExternalInvariantTensor.externalEquiv eqU (Representation.Equiv.refl WeylSpinor.right))
    (ExternalInvariantTensor.externalEquiv eqE (Representation.Equiv.refl WeylSpinor.right)))

include eqQ eqU eqE in
theorem exists_on_fields_iff :
    (∃ f : QqueCoefficientSector.sector q u e, f ≠ 0) ↔
      ∃ k : IntertwiningMap (a.symmetricPower 2) (b.tprod d), k ≠ 0 := by
  let s := onFieldsEquiv a b d q u e eqQ eqU eqE
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨s.symm f, ?_⟩
    intro hz
    apply hf
    calc f = s (s.symm f) := (s.apply_symm_apply f).symm
         _ = 0 := by rw [hz, map_zero]
  · rintro ⟨k, hk⟩
    refine ⟨s k, ?_⟩
    intro hz
    apply hk
    exact s.injective (hz.trans (map_zero s).symm)

include eqQ eqU eqE in
theorem hasNonzeroAlternation_iff :
    HasNonzeroAlternation q u e ↔
      ∃ k : IntertwiningMap (a.symmetricPower 2) (b.tprod d), k ≠ 0 :=
  (QqueCoefficientSector.hasNonzeroAlternation_iff q u e).trans
    (exists_on_fields_iff a b d q u e eqQ eqU eqE)

end
end Physics.QqueCoefficientCompleteness
