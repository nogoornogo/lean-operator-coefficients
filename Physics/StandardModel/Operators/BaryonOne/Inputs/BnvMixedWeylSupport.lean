import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvMixedInput
import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvBoundedSpecies

open Math

/-! Weyl parity on the independent four-fermion/mixed-boson carrier. -/
namespace Physics.BnvMixedWeylSupport
set_option autoImplicit false
noncomputable section
open Representation BnvMixedInput DeltaLOneSignedInput SMEpsilonTensor
open scoped TensorProduct

def scalarCount {m : ℕ} (labels : Fin m → ScalarSpecies) (s : ScalarSpecies) : ℕ :=
  (Finset.univ.filter (fun i => labels i = s)).card

theorem scalar_sum_weights {m : ℕ} (labels : Fin m → ScalarSpecies)
    {A : Type*} [AddCommMonoid A] (w : ScalarSpecies → A) :
    ∑ i, w (labels i) = ∑ s, scalarCount labels s • w s := by
  rw [← Finset.sum_fiberwise_of_maps_to' (fun i (_ : i ∈ Finset.univ) =>
    Finset.mem_univ (labels i)) w]
  simp [scalarCount, Finset.sum_const]

theorem scalar_count_sum {m : ℕ} (labels : Fin m → ScalarSpecies) :
    scalarCount labels 0 + scalarCount labels 1 = m := by
  have h := scalar_sum_weights labels (fun _ => (1 : ℕ))
  simpa [Fin.sum_univ_two] using h.symm

def mixedCounts {m : ℕ} (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies) :
    BnvBoundedSpecies.Counts := ⟨counts labels, scalarCount scalars 0, scalarCount scalars 1⟩

theorem counts_dimension {m : ℕ} (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies) :
    BnvBoundedSpecies.doubledDimension (mixedCounts labels scalars) = 12 + 2 * m := by
  simp [BnvBoundedSpecies.doubledDimension, mixedCounts, slotCount_counts, scalar_count_sum]

theorem counts_hypercharge {m : ℕ} (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies) :
    BnvBoundedSpecies.hypercharge (mixedCounts labels scalars) =
      (∑ i, hypercharge (labels i)) + (∑ j, scalarHypercharge (scalars j)) := by
  simp only [BnvBoundedSpecies.hypercharge, mixedCounts, hypercharge_counts]
  rw [scalar_sum_weights]
  simp [scalarHypercharge, Fin.sum_univ_two]
  ring

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : ScalarSpecies → Type*} [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

theorem scalarField_spinTest (s : ScalarSpecies) (x : ScalarField (S := S) s) :
    scalarField scalarFlavor s DeltaLOneSignedFields.fullSpinTest x = x := by
  have he : scalarField scalarFlavor s DeltaLOneSignedFields.fullSpinTest = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    simp [scalarField, ExternalInvariantTensor.external, DeltaLOneSignedFields.fullSpinTest,
      Representation.tprod_apply]
  rw [he]; rfl

theorem odd_basis_vanish {m : ℕ} (f : Coefficient flavor scalarFlavor 4 m)
    (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies)
    (hodd : DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 = 1)
    (a : ∀ i, DeltaLOneSignedFields.GaugeCarrier (labels i))
    (idx : Fin 4 → Fin 2) (x : ∀ i, F (labels i))
    (w : ∀ j, ScalarField (S := S) (scalars j)) :
    value flavor scalarFlavor f labels scalars
      (fun i => (a i ⊗ₜ[ℂ] weakBasis (idx i)) ⊗ₜ[ℂ] x i) w = 0 := by
  have hp := OddWeylInvariant.odd_product_ne_one
    (DeltaLOneSignedFields.rightHanded (labels 0))
    (DeltaLOneSignedFields.rightHanded (labels 1))
    (DeltaLOneSignedFields.rightHanded (labels 2))
    (DeltaLOneSignedFields.rightHanded (labels 3))
    (by simpa [DeltaLOneSignedFields.leftSlots_counts, Fin.sum_univ_succ, add_assoc] using hodd)
    (idx 0) (idx 1) (idx 2) (idx 3)
  apply MixedWeightSupport.vanish_of_scalar
    (DeltaLOneSignedFields.fullRepresentation flavor) (scalarRepresentation scalarFlavor)
    f DeltaLOneSignedFields.fullSpinTest _ _
    (fun i => OddWeylInvariant.slotEigen (DeltaLOneSignedFields.rightHanded (labels i)) (idx i))
    (fun _ => (1 : ℂ))
  · intro i
    change FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field flavor) _ _ = _
    rw [FiniteSpeciesExterior.action_single, DeltaLOneSignedFields.field_spin_basis]
    exact Pi.single_smul _ _ _
  · intro j
    change FiniteSpeciesExterior.representation (scalarField scalarFlavor) _ _ = _
    rw [FiniteSpeciesExterior.action_single, scalarField_spinTest, one_smul]
  · simp only [Finset.prod_const_one, mul_one]
    apply sub_ne_zero.mp
    convert hp using 1
    simp [Fin.prod_univ_succ, mul_assoc]

theorem odd_vanish {m : ℕ} (f : Coefficient flavor scalarFlavor 4 m)
    (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies)
    (hodd : DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 = 1)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (labels i))
    (w : ∀ j, ScalarField (S := S) (scalars j)) :
    value flavor scalarFlavor f labels scalars v w = 0 := by
  let E := ⋀[ℂ]^4 (∀ s, DeltaLOneSignedFields.Field (F := F) s)
  let B := Sym[ℂ]^m (∀ s, ScalarField (S := S) s)
  let ev := (f.toLinearMap.comp ((TensorProduct.mk ℂ E B).flip
    (SymmetricPower.tprod ℂ (fun j => Pi.single (scalars j) (w j))))).compAlternatingMap
      (exteriorPower.ιMulti ℂ 4)
  let restr := ev.toMultilinearMap.compLinearMap
    (fun i => LinearMap.single ℂ (DeltaLOneSignedFields.Field (F := F)) (labels i))
  have hz : restr = 0 := by
    let b (i : Fin 4) :=
      ((Module.Free.chooseBasis ℂ (DeltaLOneSignedFields.GaugeCarrier (labels i))).tensorProduct
        (Pi.basisFun ℂ (Fin 2))).tensorProduct (Module.Free.chooseBasis ℂ (F (labels i)))
    apply Module.Basis.ext_multilinear b
    intro idx
    change value flavor scalarFlavor f labels scalars (fun i => b i (idx i)) w = 0
    simpa only [b, Module.Basis.tensorProduct_apply', Pi.basisFun_apply, weakBasis] using
      odd_basis_vanish flavor scalarFlavor f labels scalars hodd
        (fun i => Module.Free.chooseBasis ℂ (DeltaLOneSignedFields.GaugeCarrier (labels i)) (idx i).1.1)
        (fun i => (idx i).1.2)
        (fun i => Module.Free.chooseBasis ℂ (F (labels i)) (idx i).2) w
  change restr v = 0
  rw [hz]
  rfl

theorem left_even_of_nonzero {m : ℕ} (f : Coefficient flavor scalarFlavor 4 m)
    (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (labels i))
    (w : ∀ j, ScalarField (S := S) (scalars j))
    (hf : value flavor scalarFlavor f labels scalars v w ≠ 0) :
    DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 = 0 := by
  have hn : DeltaLOneSpeciesSupport.leftSlots (counts labels) % 2 ≠ 1 := by
    intro ho
    exact hf (odd_vanish flavor scalarFlavor f labels scalars ho v w)
  omega

theorem admissible_of_nonzero {m : ℕ} (f : bnvSector flavor scalarFlavor 4 m)
    (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (labels i))
    (w : ∀ j, ScalarField (S := S) (scalars j)) (bound : ℕ)
    (hd : 12 + 2 * m ≤ 2 * bound)
    (hf : value flavor scalarFlavor f.val labels scalars v w ≠ 0) :
    BnvBoundedSpecies.Admissible bound (mixedCounts labels scalars) := by
  refine ⟨by rw [counts_dimension]; exact hd, ?_, ?_, ?_, ?_, ?_⟩
  · change DeltaLOneSpeciesSupport.threeBaryonDegree (counts labels) ≠ 0
    rw [baryon_counts]
    intro hb
    exact hf (f.property labels scalars v w hb)
  · change DeltaLOneSpeciesSupport.threeBaryonDegree (counts labels) % 3 = 0
    rw [baryon_counts]
    exact triality_of_nonzero flavor scalarFlavor f.val labels scalars v w hf
  · change DeltaLOneSpeciesSupport.slotCount (counts labels) % 2 = 0
    rw [slotCount_counts]
  · exact left_even_of_nonzero flavor scalarFlavor f.val labels scalars v w hf
  · rw [counts_hypercharge]
    exact hypercharge_of_nonzero flavor scalarFlavor f.val labels scalars v w hf

theorem seven_support_of_nonzero {m : ℕ} (f : bnvSector flavor scalarFlavor 4 m)
    (labels : Fin 4 → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (labels i))
    (w : ∀ j, ScalarField (S := S) (scalars j)) (hd : 12 + 2 * m ≤ 14)
    (hf : value flavor scalarFlavor f.val labels scalars v w ≠ 0) :
    BnvBoundedSpecies.SevenFamily (mixedCounts labels scalars) ∨
      BnvBoundedSpecies.SevenFamily (BnvBoundedSpecies.conjugate (mixedCounts labels scalars)) :=
  (BnvBoundedSpecies.admissible_le_seven_iff _).mp
    (admissible_of_nonzero flavor scalarFlavor f labels scalars v w 7 hd hf)

end
end Physics.BnvMixedWeylSupport
