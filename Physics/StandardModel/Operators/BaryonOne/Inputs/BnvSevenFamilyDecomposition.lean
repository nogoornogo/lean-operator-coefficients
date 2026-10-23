import Physics.StandardModel.Operators.BaryonOne.Inputs.BnvSevenPatternDescent
import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneFourFamilyDecomposition
import Math.RepresentationTheory.Content.MixedSingleSpeciesPartition

open Math

/-! Species-count support for both signs of the one-Higgs BNV degree. -/
namespace Physics.BnvSevenFamilyDecomposition
set_option autoImplicit false
noncomputable section
open Representation DeltaLOneSignedInput BnvMixedInput BnvMixedWeylSupport

def pattern : Fin 8 → Fin 4 → Species :=
  ![![1,2,2,8], ![0,0,2,8], ![0,2,2,9], ![2,2,2,8],
    ![6,7,7,3], ![5,5,7,3], ![5,7,7,4], ![7,7,7,3]]
def scalar : Fin 8 → ScalarSpecies := ![1,1,1,0,0,0,0,1]

def support (i : Fin 8) (labels : Fin 4 → Species) (u : ScalarSpecies) : Prop :=
  counts labels = counts (pattern i) ∧ u = scalar i
instance (i : Fin 8) (labels : Fin 4 → Species) : DecidablePred (support i labels) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem stable (i : Fin 8) (labels : Fin 4 → Species) (u : ScalarSpecies)
    (e : Equiv.Perm (Fin 4)) : support i (labels ∘ e) u ↔ support i labels u := by
  simp only [support, DeltaLOneFourFamilyDecomposition.counts_perm]

theorem disjoint (i j : Fin 8) (hij : i ≠ j) (labels : Fin 4 → Species)
    (u : ScalarSpecies) (hi : support i labels u) : ¬ support j labels u := by
  intro hj
  have he : counts (pattern i) = counts (pattern j) := hi.1.symm.trans hj.1
  have hinj : Function.Injective (fun i => counts (pattern i)) := by decide +kernel
  exact hij (hinj he)

theorem orbit_iff (i : Fin 8) (labels : Fin 4 → Species) (u : ScalarSpecies) :
    support i labels u ↔
      (∃ e : Equiv.Perm (Fin 4), labels ∘ e = pattern i) ∧ u = scalar i := by
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    apply FiniteSpeciesExterior.permutation_of_counts
    exact DeltaLOneFourFamilyDecomposition.multiplicities_eq_of_counts _ _ h.1
  · rintro ⟨⟨e, he⟩, hu⟩
    refine ⟨?_, hu⟩
    rw [← he, DeltaLOneFourFamilyDecomposition.counts_perm]

theorem pattern_baryon (i : Fin 8) : ∑ k, baryon (pattern i k) ≠ 0 := by
  fin_cases i <;> norm_num [pattern, baryon, Fin.sum_univ_succ]

def familyCounts : Fin 8 → DeltaLOneSpeciesSupport.Counts :=
  ![BnvBoundedSpecies.uddAntiL.fermions, BnvBoundedSpecies.qqdAntiL.fermions,
    BnvBoundedSpecies.qddAntiE.fermions, BnvBoundedSpecies.dddAntiL.fermions,
    (BnvBoundedSpecies.conjugate BnvBoundedSpecies.uddAntiL).fermions,
    (BnvBoundedSpecies.conjugate BnvBoundedSpecies.qqdAntiL).fermions,
    (BnvBoundedSpecies.conjugate BnvBoundedSpecies.qddAntiE).fermions,
    (BnvBoundedSpecies.conjugate BnvBoundedSpecies.dddAntiL).fermions]

theorem counts_pattern (i : Fin 8) : counts (pattern i) = familyCounts i := by
  fin_cases i <;> decide +kernel

theorem single_scalar_support (c : DeltaLOneSpeciesSupport.Counts) (u : ScalarSpecies)
    (h : BnvBoundedSpecies.SevenFamily
        ⟨c, if u = 0 then 1 else 0, if u = 1 then 1 else 0⟩ ∨
      BnvBoundedSpecies.SevenFamily (BnvBoundedSpecies.conjugate
        ⟨c, if u = 0 then 1 else 0, if u = 1 then 1 else 0⟩)) :
    ∃ i : Fin 8, c = familyCounts i ∧ u = scalar i := by
  cases c
  fin_cases u <;>
    simpa [BnvBoundedSpecies.SevenFamily, BnvBoundedSpecies.dimSix,
      BnvBoundedSpecies.conjugate, BnvBoundedSpecies.uddAntiL,
      BnvBoundedSpecies.qqdAntiL, BnvBoundedSpecies.qddAntiE,
      BnvBoundedSpecies.dddAntiL, familyCounts, scalar, Fin.exists_fin_succ,
      and_assoc, and_comm, and_left_comm, or_assoc] using h

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : ScalarSpecies → Type*} [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

theorem support_of_nonzero (f : bnvSector flavor scalarFlavor 4 1)
    (labels : Fin 4 → Species) (u : ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (labels i))
    (w : ScalarField (S := S) u)
    (hf : value flavor scalarFlavor f.val labels (fun _ : Fin 1 => u) v
      (fun _ : Fin 1 => w) ≠ 0) : ∃ i : Fin 8, support i labels u := by
  have hs := seven_support_of_nonzero flavor scalarFlavor f labels
    (fun _ : Fin 1 => u) v (fun _ : Fin 1 => w) (by omega) hf
  have he : mixedCounts labels (fun _ : Fin 1 => u) =
      ⟨counts labels, if u = 0 then 1 else 0, if u = 1 then 1 else 0⟩ := by
    fin_cases u <;> simp [mixedCounts, scalarCount, Finset.univ_unique]
  rw [he] at hs
  obtain ⟨i, hi, hu⟩ := single_scalar_support (counts labels) u hs
  exact ⟨i, by rw [support, counts_pattern]; exact ⟨hi, hu⟩⟩

abbrev FamilySector (i : Fin 8) := MixedSingleSpeciesProjection.supportSpace
  (DeltaLOneSignedFields.field flavor) (scalarField scalarFlavor) (support i)

theorem sector_eq_partition : bnvSector flavor scalarFlavor 4 1 =
    MixedSingleSpeciesPartition.partitionSpace (DeltaLOneSignedFields.field flavor)
      (scalarField scalarFlavor) support := by
  apply Submodule.ext
  intro f
  constructor
  · intro hf labels u v w hout
    by_contra hn
    exact hout (support_of_nonzero flavor scalarFlavor ⟨f, hf⟩ labels u v w hn)
  · intro hf labels scalars v w hb
    have hout : ¬ ∃ i : Fin 8, support i labels (scalars 0) := by
      rintro ⟨i, hi⟩
      have hsum : (∑ k, baryon (labels k)) = ∑ k, baryon (pattern i k) := by
        rw [← baryon_counts, ← baryon_counts, hi.1]
      exact pattern_baryon i (hsum.symm.trans hb)
    have hw : (fun j => Pi.single (scalars j) (w j)) =
        fun _ : Fin 1 => Pi.single (scalars 0) (w 0) := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rfl
    change f (MixedWeightSupport.pure _ _) = 0
    rw [hw]
    exact hf labels (scalars 0) v (w 0) hout

/-- Full independent degree `(4,1)` input, not a selected contraction ansatz. -/
def equiv : bnvSector flavor scalarFlavor 4 1 ≃ₗ[ℂ]
    (∀ i : Fin 8, FamilySector flavor scalarFlavor i) :=
  MixedSingleSpeciesPartition.equivOfEq (DeltaLOneSignedFields.field flavor)
    (scalarField scalarFlavor) support stable disjoint _
    (sector_eq_partition flavor scalarFlavor)

theorem familySpace_eq (i : Fin 8) :
    MixedSingleSpeciesProjection.supportSpace (DeltaLOneSignedFields.field flavor)
      (scalarField scalarFlavor) (support i) =
    MixedSinglePatternAssembly.familySpace (DeltaLOneSignedFields.field flavor)
      (scalarField scalarFlavor) (pattern i) (scalar i) := by
  apply Submodule.ext
  intro f
  change (∀ (labels : Fin 4 → Species) (u : ScalarSpecies)
    (v : ∀ j, DeltaLOneSignedFields.Field (F := F) (labels j))
    (w : ScalarField (S := S) u), ¬ support i labels u → f (MixedWeightSupport.pure
      (fun j => Pi.single (labels j) (v j)) (fun _ : Fin 1 => Pi.single u w)) = 0) ↔
    (∀ (labels : Fin 4 → Species) (u : ScalarSpecies)
    (v : ∀ j, DeltaLOneSignedFields.Field (F := F) (labels j))
    (w : ScalarField (S := S) u),
      (¬ ∃ e : Equiv.Perm (Fin 4), labels ∘ e = pattern i) ∨ u ≠ scalar i →
      f (MixedWeightSupport.pure (fun j => Pi.single (labels j) (v j))
        (fun _ : Fin 1 => Pi.single u w)) = 0)
  simp only [orbit_iff, not_and_or]

abbrev OrderedSector (i : Fin 8) := MixedSinglePatternAssembly.orderedSpace
  (DeltaLOneSignedFields.field flavor) (scalarField scalarFlavor) (pattern i) (scalar i)

def familyEquiv (i : Fin 8) : FamilySector flavor scalarFlavor i ≃ₗ[ℂ]
    OrderedSector flavor scalarFlavor i :=
  (LinearEquiv.ofEq _ _ (familySpace_eq flavor scalarFlavor i)).trans
    (MixedSinglePatternAssembly.equiv (DeltaLOneSignedFields.field flavor)
      (scalarField scalarFlavor) (pattern i) (scalar i))

/-- Extraction and reconstruction on all eight actual typed patterns. -/
def orderedEquiv : bnvSector flavor scalarFlavor 4 1 ≃ₗ[ℂ]
    (∀ i : Fin 8, OrderedSector flavor scalarFlavor i) :=
  (equiv flavor scalarFlavor).trans
    (LinearEquiv.piCongrRight (familyEquiv flavor scalarFlavor))

theorem nonzero_iff : (∃ f : bnvSector flavor scalarFlavor 4 1, f ≠ 0) ↔
    ∃ i : Fin 8, ∃ f : OrderedSector flavor scalarFlavor i, f ≠ 0 :=
  FiniteSpeciesProjection.nonzero_iff_pi
    (A := bnvSector flavor scalarFlavor 4 1) (J := Fin 8)
    (B := fun i => OrderedSector flavor scalarFlavor i)
    (orderedEquiv flavor scalarFlavor)

theorem forbidden_iff : (∀ f : bnvSector flavor scalarFlavor 4 1, f = 0) ↔
    ∀ i : Fin 8, ∀ f : OrderedSector flavor scalarFlavor i, f = 0 := by
  simpa only [not_exists, not_not] using not_congr (nonzero_iff flavor scalarFlavor)

end
end Physics.BnvSevenFamilyDecomposition
