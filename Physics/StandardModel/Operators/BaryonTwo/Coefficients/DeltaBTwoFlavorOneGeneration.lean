import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoFlavorBridge
import Physics.StandardModel.Operators.BaryonTwo.Coefficients.SixQuarkFlavorOneGeneration

open Math

/-! Scalar residual multiplicities and the physical two-probe classification. -/
namespace Physics.DeltaBTwoFlavorOneGeneration
set_option autoImplicit false
noncomputable section
open SixQuarkInvariant SixQuarkSpeciesQuotient SixQuarkFlavorCoordinates
open SixQuarkTypedFlavor DeltaBTwoFlavorBridge
open scoped TensorProduct

abbrev scalar : Representation ℂ Unit ℂ := Representation.trivial ℂ Unit ℂ

def scalarFiber (b : Bool) : Flavor ℂ ℂ b ≃ₗ[ℂ] ℂ :=
  match b with | true => LinearEquiv.refl ℂ ℂ | false => LinearEquiv.refl ℂ ℂ

def strip (i : Fin 6) : Quark ⊗[ℂ] SlotFlavor ℂ ℂ i ≃ₗ[ℂ] Quark :=
  (TensorProduct.congr (LinearEquiv.refl ℂ Quark)
    (scalarFiber (decide (i = 0 ∨ i = 2)))).trans (TensorProduct.rid ℂ Quark)

theorem strip_map (a : Quark →ₗ[ℂ] Quark) (i : Fin 6)
    (v : Quark ⊗[ℂ] SlotFlavor ℂ ℂ i) :
    strip i (TensorProduct.map a LinearMap.id v) = a (strip i v) := by
  have he : (strip i).toLinearMap.comp (TensorProduct.map a LinearMap.id) =
      a.comp (strip i).toLinearMap := by
    apply TensorProduct.ext
    ext q t
    simp [strip]
  exact DFunLike.congr_fun he v

theorem strip_symm_map (a : Quark →ₗ[ℂ] Quark) (i : Fin 6) (q : Quark) :
    (strip i).symm (a q) = TensorProduct.map a LinearMap.id ((strip i).symm q) := by
  apply (strip i).injective
  simp only [LinearEquiv.apply_symm_apply, strip_map]

theorem strip_exchange (g : Fin 4) (i : Fin 6)
    (v : Quark ⊗[ℂ] SlotFlavor ℂ ℂ (slotSwap g i)) :
    strip i (tensorExchange ℂ ℂ g i v) = strip (slotSwap g i) v := by
  let e := TensorProduct.congr (LinearEquiv.refl ℂ Quark) (LinearEquiv.refl ℂ ℂ)
  fin_cases g <;> fin_cases i
  all_goals change (TensorProduct.rid ℂ Quark) (e (e v)) = (TensorProduct.rid ℂ Quark) (e v)
  all_goals simp only [e, TensorProduct.congr_refl_refl, LinearEquiv.refl_apply]

theorem strip_exchange_symm (g : Fin 4) (i : Fin 6) (q : Quark) :
    tensorExchange ℂ ℂ g i ((strip (slotSwap g i)).symm q) = (strip i).symm q := by
  apply (strip i).injective
  simp only [strip_exchange, LinearEquiv.apply_symm_apply]

def forget (f : Coefficients ℂ ℂ scalar scalar) : admissible := by
  let k : Coefficient := f.val.compLinearMap (fun i => (strip i).symm.toLinearMap)
  refine ⟨k, ⟨?_, ?_⟩, ?_⟩
  · intro g v
    change f.val (fun i => (strip i).symm (colorAction g (v i))) = _
    simp_rw [strip_symm_map]
    exact f.property.1.1 g _
  · intro g v
    change f.val (fun i => (strip i).symm (spinAction g (v i))) = _
    simp_rw [strip_symm_map]
    exact f.property.1.2 g _
  · intro p hp v
    apply generators_species_sign k _ p hp v
    intro g w
    have he := typed_swap_full ℂ ℂ f.val f.property.2.2 g (fun i => (strip i).symm (w i))
    simpa only [strip_exchange_symm, k, MultilinearMap.compLinearMap_apply, LinearEquiv.coe_coe,
      Function.comp_def] using he

def add (f : admissible) : Coefficients ℂ ℂ scalar scalar := by
  refine ⟨f.val.compLinearMap (fun i => (strip i).toLinearMap), ⟨?_, ?_⟩, ?_, ?_⟩
  · intro g v
    change f.val (fun i => strip i (TensorProduct.map (colorAction g) LinearMap.id (v i))) = _
    simp_rw [strip_map]
    exact f.property.1.1 g _
  · intro g v
    change f.val (fun i => strip i (TensorProduct.map (spinAction g) LinearMap.id (v i))) = _
    simp_rw [strip_map]
    exact f.property.1.2 g _
  · intro g v
    have hr (i : Fin 6) : slotRepresentation ℂ ℂ scalar scalar i g = LinearMap.id := by
      unfold slotRepresentation flavorRepresentation scalar
      cases decide (i = 0 ∨ i = 2) <;> rfl
    simp only [MultilinearMap.compLinearMap_apply]
    simp [hr]
  · intro g q t
    have hp : SixSlotAlternation.PreservesPattern (slotSwap g) := by fin_cases g <;> decide
    have he := f.property.2 (slotSwap g) hp (fun i => strip i (q i ⊗ₜ[ℂ] t i))
    have hs : Equiv.Perm.sign (slotSwap g) = -1 := by fin_cases g <;> decide
    rw [hs] at he
    change f.val (fun i => strip i (q (slotSwap g i) ⊗ₜ[ℂ] exchangeFlavor g
      (speciesExchange ℂ ℂ g) t i)) = -f.val (fun i => strip i (q i ⊗ₜ[ℂ] t i))
    have hx (i : Fin 6) := strip_exchange g i (q (slotSwap g i) ⊗ₜ[ℂ] t (slotSwap g i))
    simp only [tensorExchange, TensorProduct.congr_tmul, LinearEquiv.refl_apply] at hx
    simp only [exchangeFlavor, hx]
    simpa only [Function.comp_def, Units.neg_smul, one_smul] using he

def typedScalarEquiv : Coefficients ℂ ℂ scalar scalar ≃ₗ[ℂ] admissible where
  toFun := forget
  invFun := add
  left_inv f := by
    apply Subtype.ext
    ext v
    change f.val (fun i => (strip i).symm (strip i (v i))) = f.val v
    simp only [LinearEquiv.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    ext v
    change f.val (fun i => strip i ((strip i).symm (v i))) = f.val v
    simp only [LinearEquiv.apply_symm_apply]
  map_add' f k := by apply Subtype.ext; ext v; rfl
  map_smul' z f := by apply Subtype.ext; ext v; rfl

def physicalTwoProbeEquiv : DeltaBTwoModelInterface.ModelSector scalar scalar ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (sectorCoefficientEquiv scalar scalar).trans (typedScalarEquiv.trans coefficientProbeEquiv)

theorem inverse_twoProbes (f : DeltaBTwoModelInterface.ModelSector scalar scalar) :
    physicalTwoProbeEquiv.symm (physicalTwoProbeEquiv f) = f :=
  physicalTwoProbeEquiv.symm_apply_apply f

theorem physicalTwoProbeEquiv_symm_apply (t : Fin 2 → ℂ) :
    physicalTwoProbeEquiv.symm t = liftSector scalar scalar (add (fromProbesCoefficient t)) := rfl

def homTwoProbeEquiv : StatisticsHom ℂ ℂ scalar scalar ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (sectorHomEquiv scalar scalar).symm.trans physicalTwoProbeEquiv

theorem finrank_hom : Module.finrank ℂ (StatisticsHom ℂ ℂ scalar scalar) = 2 := by
  rw [homTwoProbeEquiv.finrank_eq]
  simp

theorem finrank_physical :
    Module.finrank ℂ (DeltaBTwoModelInterface.ModelSector scalar scalar) = 2 := by
  rw [physicalTwoProbeEquiv.finrank_eq]
  simp

section ActualFields
variable {A B : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  (a : Representation ℂ (DeltaBTwoModelInterface.SymmetryGroup Unit) A)
  (b : Representation ℂ (DeltaBTwoModelInterface.SymmetryGroup Unit) B)
  (input : DeltaBTwoModelInterface.Inputs scalar scalar a b)

def onFieldsTwoProbeEquiv : SixSlotSpeciesDegree.sector a b ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  (DeltaBTwoModelInterface.onFieldsEquiv scalar scalar a b input).symm.trans physicalTwoProbeEquiv

include input in
theorem finrank_onFields : Module.finrank ℂ (SixSlotSpeciesDegree.sector a b) = 2 := by
  rw [(onFieldsTwoProbeEquiv a b input).finrank_eq]
  simp

end ActualFields

end
end Physics.DeltaBTwoFlavorOneGeneration
