import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenCompleteness
import Physics.StandardModel.Operators.Selection.CyclicResidualSelection

open Math

/-! Finite cyclic controls on the whole bound-seven input, including both
signs and neutral Higgs actions. These are coefficient-existence statements. -/
namespace Physics.BnvSevenControls
set_option autoImplicit false
noncomputable section
open Representation BnvMixedInput DeltaLOneSignedInput CyclicCharge
open scoped TensorProduct

def scalarFlavor (_ : ScalarSpecies) : Representation ℂ (CyclicCharge.Group 2) ℂ :=
  Representation.trivial ℂ _ ℂ
def parityFlavor := CyclicResidualSelection.flavor CyclicResidualSelection.quarkParity
def generator : CyclicCharge.Group 2 := Multiplicative.ofAdd 1
def phase : ℂ := ZMod.stdAddChar (1 : ZMod 2)
def bit : Species → ℕ := ![1,1,1,0,0,1,1,1,0,0]

theorem phase_cubed_ne_one : phase ^ 3 ≠ 1 := by
  have h : phase ^ 3 = ZMod.stdAddChar (3 : ZMod 2) := by
    rw [show (3 : ZMod 2) = 1 + 1 + 1 by decide]
    simp only [AddChar.map_add_eq_mul, phase]
    ring
  rw [h]
  intro he
  have hh : ZMod.stdAddChar (3 : ZMod 2) = ZMod.stdAddChar (0 : ZMod 2) := by simpa using he
  have hz := ZMod.injective_stdAddChar hh
  exact (by decide : (3 : ZMod 2) ≠ 0) hz

def fullGenerator : (StandardSMGaugeTensor.GaugeGroup × WeylSpinor.Group) × CyclicCharge.Group 2 :=
  (1,generator)

theorem field_action (s : Species) (v : DeltaLOneSignedFields.Field (F := fun _ => ℂ) s) :
    DeltaLOneSignedFields.field parityFlavor s fullGenerator v = phase ^ bit s • v := by
  have h :
    DeltaLOneSignedFields.field parityFlavor s fullGenerator =
      phase ^ bit s • LinearMap.id := by
        apply TensorProduct.ext'
        intro x y
        change (DeltaLOneSignedFields.localField s 1 x) ⊗ₜ[ℂ]
          parityFlavor s generator y = phase ^ bit s • (x ⊗ₜ[ℂ] y)
        rw [map_one]
        fin_cases s <;>
          simp [parityFlavor, CyclicResidualSelection.flavor, CyclicResidualSelection.signedCharges,
            CyclicResidualSelection.quarkParity, CyclicCharge.action, generator, phase, bit,
            bit]
        all_goals exact TensorProduct.tmul_smul (R := ℂ) (ZMod.stdAddChar (1 : ZMod 2)) x y
  exact LinearMap.congr_fun h v

theorem scalar_action (s : ScalarSpecies) (v : ScalarField (S := fun _ => ℂ) s) :
    scalarField scalarFlavor s fullGenerator v = v := by
  have h : scalarField scalarFlavor s fullGenerator = LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    change (scalarGauge s 1 x) ⊗ₜ[ℂ] y = x ⊗ₜ[ℂ] y
    rw [map_one]
    rfl
  exact LinearMap.congr_fun h v

theorem sum_bit (labels : Fin 4 → Species) :
    ∑ i, bit (labels i) = (counts labels).q + (counts labels).u + (counts labels).d +
      (counts labels).cq + (counts labels).cu + (counts labels).cd := by
  rw [sum_weights]
  simp [bit, counts, Fin.sum_univ_succ]
  omega

theorem quark_count (labels : Fin 4 → Species) (hb : ∑ i, baryon (labels i) ≠ 0)
    (ht : (∑ i, baryon (labels i)) % 3 = 0) : ∑ i, bit (labels i) = 3 := by
  rw [sum_bit]
  rw [← baryon_counts] at hb ht
  have hs := slotCount_counts labels
  rcases hn : counts labels with ⟨q,u,d,l,e,cq,cu,cd,cl,ce⟩
  rw [hn] at hs hb ht
  simp only [DeltaLOneSpeciesSupport.slotCount, DeltaLOneSpeciesSupport.threeBaryonDegree]
    at hs hb ht
  dsimp only at hs hb ht ⊢
  have hn : q + u + d + cq + cu + cd ≤ 4 := by omega
  have hnZ : (q : ℤ) + u + d + cq + cu + cd ≤ 4 := by exact_mod_cast hn
  have hd : (q : ℤ) + u + d - cq - cu - cd = 3 ∨
      (q : ℤ) + u + d - cq - cu - cd = -3 := by omega
  have he : (q : ℤ) + u + d + cq + cu + cd = 3 := by
    rcases hd with hd | hd <;> omega
  exact_mod_cast he

theorem degree_forbidden {m : ℕ} (f : bnvSector parityFlavor scalarFlavor 4 m) : f = 0 := by
  apply Subtype.ext
  apply value_ext parityFlavor scalarFlavor
  intro labels scalars v w
  change value parityFlavor scalarFlavor f.val labels scalars v w = 0
  by_contra hn
  have hb : ∑ i, baryon (labels i) ≠ 0 := by
    intro h
    exact hn (f.property labels scalars v w h)
  have ht := triality_of_nonzero parityFlavor scalarFlavor f.val labels scalars v w hn
  have hq := quark_count labels hb ht
  have hz := MixedWeightSupport.scalar_constraint
    (A := ∀ s, DeltaLOneSignedFields.Field (F := fun _ => ℂ) s)
    (B := ∀ s, ScalarField (S := fun _ => ℂ) s)
    (DeltaLOneSignedFields.fullRepresentation parityFlavor) (scalarRepresentation scalarFlavor)
    f.val fullGenerator (fun i => Pi.single (labels i) (v i))
    (fun j => Pi.single (scalars j) (w j)) (fun i => phase ^ bit (labels i)) (fun _ => (1 : ℂ))
    (by
      intro i
      change FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field parityFlavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, field_action]
      exact Pi.single_smul _ _ _)
    (by
      intro j
      change FiniteSpeciesExterior.representation (scalarField scalarFlavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, scalar_action]
      simp)
  have hp : (∏ i, phase ^ bit (labels i)) = phase ^ 3 := by
    rw [Finset.prod_pow_eq_pow_sum, hq]
  simp only [hp, Finset.prod_const_one, mul_one] at hz
  exact hn ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr phase_cubed_ne_one))

theorem quarkParity_forbidden (f : bounded parityFlavor scalarFlavor 7) : f = 0 := by
  apply (BnvSevenDegreeDecomposition.equiv parityFlavor scalarFlavor).injective
  exact Prod.ext (degree_forbidden _) (degree_forbidden _)

def neutralFlavor := CyclicResidualSelection.flavor (0 : CyclicResidualSelection.Charges 2)

def unitResidual : BnvSixResidualCompleteness.ResidualProduct neutralFlavor :=
  ((ScalarResidualSelection.coefficient (neutralFlavor 2) (neutralFlavor 1)
    (neutralFlavor 0) (neutralFlavor 3) (by intro g; simp [
      neutralFlavor, CyclicResidualSelection.flavor, CyclicResidualSelection.signedCharges,
      CyclicCharge.action]), 0, 0, 0), 0)

theorem unitResidual_ne_zero : unitResidual ≠ 0 := by
  intro h
  have he := congrArg (fun q : BnvSixResidualCompleteness.ResidualProduct neutralFlavor =>
    q.1.1 (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1))) h
  have hv : unitResidual.1.1 (((1 : ℂ) ⊗ₜ[ℂ] 1) ⊗ₜ[ℂ] ((1 : ℂ) ⊗ₜ[ℂ] 1)) = 1 := by
    change ((TensorProduct.lift (LinearMap.mul ℂ ℂ)).comp
      (TensorProduct.map (TensorProduct.lift (LinearMap.mul ℂ ℂ))
        (TensorProduct.lift (LinearMap.mul ℂ ℂ)))) _ = 1
    simp
  rw [hv] at he
  simp at he

def positiveControl : bounded neutralFlavor scalarFlavor 7 :=
  BnvSevenCompleteness.reconstruct neutralFlavor scalarFlavor (unitResidual,0)

theorem positiveControl_ne_zero : positiveControl ≠ 0 := by
  intro h
  have he := congrArg (BnvSevenCompleteness.extract neutralFlavor scalarFlavor) h
  have hz : (unitResidual, (0 : ∀ i, BnvSevenSignedCoordinates.Factor neutralFlavor scalarFlavor i)) = 0 := by
    simpa only [positiveControl, BnvSevenCompleteness.extract_reconstruct, map_zero] using he
  exact unitResidual_ne_zero (congrArg Prod.fst hz)

end
end Physics.BnvSevenControls
