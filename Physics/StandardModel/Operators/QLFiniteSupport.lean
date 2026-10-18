import Physics.StandardModel.Operators.SMFiniteHiggsSupport
import Physics.StandardModel.Operators.DuqlHiggsContent
import Math.RepresentationTheory.ScalarResidualSupport

/-! Exact q/l residual separation in the actual finite Higgs support table.
Local gauge/Weyl support is still a separate proof obligation. -/
namespace GUT.QLFiniteSupport
set_option autoImplicit false
noncomputable section
open Math Representation BoundedHiggsSupport
open scoped TensorProduct
variable {k : ℕ} [NeZero k] (q l : ZMod k)
  {n : ℕ} (p : Fin n → DeltaLOneSignedInput.Species)

def flavor : ∀ s, Representation ℂ (CyclicCharge.Group k) (ThreeGenerationFermionBound.Flavor s) :=
  DuqlHiggsContent.fermionFlavor q l
def charge : ZMod k := ∑ i, DuqlHiggsContent.signedCharge q l (p i)
abbrev source := SMFiniteHiggsSupport.source (flavor q l) p
abbrev boson (m : ℕ) (delta : ℤ) :=
  BoundedHiggsSupport.constituent
    (SMHiggsConstituents.weakProjection (H := CyclicCharge.Group k))
    SMHiggsConstituents.character m delta
abbrev action (m : ℕ) (delta : ℤ) := (source q l p).tprod (boson (k := k) m delta)
abbrev Test (m : ℕ) (delta : ℤ) := SMFiniteHiggsSupport.Test (flavor q l) p m delta
abbrev LocalTest (m : ℕ) (delta : ℤ) := ScalarResidualSupport.Local (action q l p m delta)

theorem character_product (g : CyclicCharge.Group k) :
    (∏ i, MixedChargeSelection.cyclicCharacter g (DuqlHiggsContent.signedCharge q l (p i))) =
      MixedChargeSelection.cyclicCharacter g (charge q l p) := by
  have he := MixedChargeSelection.total_eq_character (MixedChargeSelection.cyclicCharacter g)
    (DuqlHiggsContent.signedCharge q l) (fun _ : Fin 1 => (0 : ZMod k)) p
    (fun i : Fin 0 => Fin.elim0 i)
  simpa only [MixedScalarSelection.total, MixedChargeSelection.charge,
    Finset.prod_empty, Finset.univ_eq_empty, Finset.sum_empty, add_zero, mul_one, charge] using he

theorem raw_residual (g : CyclicCharge.Group k) :
    PatternExteriorSource.Raw (DeltaLOneSignedFields.field (flavor q l)) p (1,g) =
      MixedChargeSelection.cyclicCharacter g (charge q l p) • LinearMap.id := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply,
    MultilinearInvariantHom.tensorRepresentation_tprod, LinearMap.smul_apply, LinearMap.id_apply]
  have hb (i : Fin n) : DeltaLOneSignedFields.field (flavor q l) (p i) (1,g) (v i) =
      MixedChargeSelection.cyclicCharacter g (DuqlHiggsContent.signedCharge q l (p i)) • v i :=
    DuqlHiggsContent.field_scalar q l g (p i) (v i)
  simp_rw [hb]
  rw [(PiTensorProduct.tprod ℂ).map_smul_univ, character_product]

theorem source_residual (g : CyclicCharge.Group k)
    (x : PatternExteriorSource.Source (DeltaLOneSignedFields.field (flavor q l)) p) :
    source q l p (1,g) x = MixedChargeSelection.cyclicCharacter g (charge q l p) • x :=
  PatternExteriorSource.source_scalar (DeltaLOneSignedFields.field (flavor q l)) p
    (1,g) _ (raw_residual q l p g) x

omit [NeZero k] in
theorem boson_residual (m : ℕ) (delta : ℤ) (g : CyclicCharge.Group k)
    (v : Sym[ℂ]^m WeakDoubletScalars.Doublet) : boson (k := k) m delta (1,g) v = v := by
  have hc : SMHiggsConstituents.character (H := CyclicCharge.Group k) (1,g) = 1 := by
    apply Units.ext
    simp [SMHiggsConstituents.character_apply, StandardSMGaugeTensor.phase]
  change ((SMHiggsConstituents.character^delta) (1,g) : ℂˣ) •
    (WeakDoubletScalars.doublet.symmetricPower m) 1 v = v
  simp [hc]

theorem action_residual (m : ℕ) (delta : ℤ) (g : CyclicCharge.Group k)
    (x : (PatternExteriorSource.Source (DeltaLOneSignedFields.field (flavor q l)) p) ⊗[ℂ]
      Sym[ℂ]^m WeakDoubletScalars.Doublet) :
    action q l p m delta (1,g) x = MixedChargeSelection.cyclicCharacter g (charge q l p) • x := by
  have he : action q l p m delta (1,g) =
      MixedChargeSelection.cyclicCharacter g (charge q l p) • LinearMap.id := by
    apply TensorProduct.ext'
    intro v w
    simp only [action, Representation.tprod_apply, TensorProduct.map_tmul,
      source_residual, boson_residual, LinearMap.smul_apply, LinearMap.id_apply,
      ← TensorProduct.smul_tmul']
  exact LinearMap.congr_fun he x

theorem test_allowed_iff (m : ℕ) (delta : ℤ) :
    SelectionCriteria.Allowed (Test q l p m delta) ↔ charge q l p = 0 ∧
      SelectionCriteria.Allowed (LocalTest q l p m delta) := by
  have he := ScalarResidualSupport.allowed_iff (action q l p m delta)
    (fun g => MixedChargeSelection.cyclicCharacter g (charge q l p)) (action_residual q l p m delta)
  exact he.trans (and_congr (CyclicCharge.neutral_iff _) Iff.rfl)

theorem field_local (s : DeltaLOneSignedInput.Species)
    (g : StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group)
    (x : DeltaLOneSignedFields.Field (F := ThreeGenerationFermionBound.Flavor) s) :
    DeltaLOneSignedFields.field (flavor q l) s (g,1) x =
      DeltaLOneSignedFields.field (flavor (0 : ZMod k) 0) s (g,1) x := by
  have he : DeltaLOneSignedFields.field (flavor q l) s (g,1) =
      DeltaLOneSignedFields.field (flavor (0 : ZMod k) 0) s (g,1) := by
    apply TensorProduct.ext'
    intro a b
    simp [DeltaLOneSignedFields.field, ExternalInvariantTensor.external,
      Representation.tprod_apply]
  exact LinearMap.congr_fun he x

theorem original_allowed_iff (h d : ℕ) :
    SelectionCriteria.Allowed (SMFiniteHiggsSupport.OriginalSpace (flavor q l) p h d) ↔
    charge q l p = 0 ∧ ∃ m : Fin (SMContentWeakBound.bound p+1), Admissible h d m.val ∧
      SelectionCriteria.Allowed (LocalTest q l p m.val ((h : ℤ)-d)) :=
  (SMFiniteHiggsSupport.original_allowed_iff (flavor q l) p h d).trans
    (ScalarResidualSupport.exists_guard_iff
      (fun m : Fin (SMContentWeakBound.bound p+1) => Admissible h d m.val)
      (fun m => SelectionCriteria.Allowed (Test q l p m.val ((h : ℤ)-d)))
      (fun m => SelectionCriteria.Allowed (LocalTest q l p m.val ((h : ℤ)-d)))
      (charge q l p=0) (fun m => test_allowed_iff q l p m.val ((h : ℤ)-d)))

omit [NeZero k] in
theorem family_charge_controls :
    charge q l (![2,1,0,3] : Fin 4 → DeltaLOneSignedInput.Species) = 3*q+l ∧
    charge q l (![0,0,1,4] : Fin 4 → DeltaLOneSignedInput.Species) = 3*q+l ∧
    charge q l (![0,0,0,3] : Fin 4 → DeltaLOneSignedInput.Species) = 3*q+l ∧
    charge q l (![2,1,1,4] : Fin 4 → DeltaLOneSignedInput.Species) = 3*q+l ∧
    charge q l (![1,1,2,2,2,2] : Fin 6 → DeltaLOneSignedInput.Species) = 6*q ∧
    charge q l (![3,3] : Fin 2 → DeltaLOneSignedInput.Species) = 2*l := by
  simp [charge, DuqlHiggsContent.signedCharge, Fin.sum_univ_succ]
  ring_nf
  simp

end
end GUT.QLFiniteSupport
