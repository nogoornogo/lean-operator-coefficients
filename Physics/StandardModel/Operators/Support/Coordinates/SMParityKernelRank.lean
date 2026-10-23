import Physics.StandardModel.Operators.Support.Coordinates.SMFullLocalKernel
import Math.RepresentationTheory.Protection.MixedScalarSelection

/-! Odd total fermion degree has full local constraint rank for every content. -/
namespace Physics.SMParityKernelRank
set_option autoImplicit false
noncomputable section
open Math Representation
open scoped TensorProduct
variable {H : Type*} [Group H]
  (flavor : ∀ s, Representation ℂ H (ThreeGenerationFermionBound.Flavor s))
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

theorem raw_minus : PatternExteriorSource.Raw (DeltaLOneSignedFields.field flavor) p
    BnvMixedInput.fullMinus = (-1 : ℂ)^n • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,
    MultilinearInvariantHom.tensorRepresentation_tprod]
  simp_rw [BnvMixedInput.field_minus]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ]
  simp

theorem source_minus (x : PatternExteriorSource.Source (DeltaLOneSignedFields.field flavor) p) :
    SMIntegralLocalWeights.source flavor p (1,WeylCentralParity.minusIdentity) x =
      (-1 : ℂ)^n • x :=
  PatternExteriorSource.source_scalar (DeltaLOneSignedFields.field flavor) p
    BnvMixedInput.fullMinus ((-1 : ℂ)^n) (raw_minus flavor p) x

theorem action_minus (m : ℕ) (delta : ℤ) :
    SMIntegralLocalWeights.action flavor p m delta (1,WeylCentralParity.minusIdentity) =
      (-1 : ℂ)^n • LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  change (SMIntegralLocalWeights.source flavor p (1,WeylCentralParity.minusIdentity) x) ⊗ₜ[ℂ]
    (SMIntegralLocalWeights.boson (H := H) m delta (1,WeylCentralParity.minusIdentity) y) =
      (-1 : ℂ)^n • (x ⊗ₜ[ℂ] y)
  have hb : SMIntegralLocalWeights.boson (H := H) m delta (1,WeylCentralParity.minusIdentity) y = y :=
    SMWeylFiniteKernel.boson_fixed m delta WeylCentralParity.minusIdentity y
  rw [source_minus, hb, TensorProduct.smul_tmul']

theorem forbidden (m : ℕ) (delta : ℤ) (hn : n % 2 ≠ 0) :
    SelectionCriteria.Forbidden (InvariantCoefficientTransport.Invariants
      (SMIntegralLocalWeights.action flavor p m delta)) := by
  have ho : Odd n := Nat.odd_iff.mpr (by omega)
  apply MixedScalarSelection.invariant_zero _ (1,WeylCentralParity.minusIdentity) ((-1 : ℂ)^n)
    (by rw [ho.neg_one_pow]; norm_num)
  intro x
  exact LinearMap.congr_fun (action_minus flavor p m delta) x

theorem full_rank (m : ℕ) (delta : ℤ) (hn : n % 2 ≠ 0) :
    Module.finrank ℂ (LinearMap.range (SMFullLocalKernel.constraints flavor p m delta)) =
      Module.finrank ℂ (SMFullLocalKernel.Carrier flavor p m) := by
  have hf := (SelectionCriteria.forbidden_iff_not_allowed _).mp (forbidden flavor p m delta hn)
  have hlo := not_lt.mp (fun hr => hf ((SMFullLocalKernel.allowed_iff_rank_lt flavor p m delta).mpr hr))
  have hhi := LinearMap.finrank_range_le (SMFullLocalKernel.constraints flavor p m delta)
  simp only [Fintype.card_fin, Module.finrank_pi] at hhi hlo
  exact le_antisymm hhi hlo

end
end Physics.SMParityKernelRank
