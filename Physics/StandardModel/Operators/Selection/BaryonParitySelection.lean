import Physics.StandardModel.Operators.Selection.ComposableBLSupport
import Math.RepresentationTheory.Weights.CyclicCharge
import Math.RepresentationTheory.Jets.DerivativeProhibition

namespace Physics.BaryonParitySelection
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
open scoped BigOperators TensorProduct

/-- The integral covering character 6B, Higgs neutral. -/
def fq (u : Species) : ℤ := 2 * baryon u
def bq (_ : BnvMixedInput.ScalarSpecies) : ℤ := 0

def total {n m : ℕ} (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies) : ℤ :=
  MixedChargeSelection.charge fq bq p s

theorem total_baryon {n m : ℕ} (p : Fin n → Species)
    (s : Fin m → BnvMixedInput.ScalarSpecies) : total p s = 2 * ∑ i, baryon (p i) := by
  simp [total,MixedChargeSelection.charge,fq,bq,Finset.mul_sum]

section Copies
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def copies (q : ZMod 4) : Representation ℂ (CyclicCharge.Group 4) V where
  toFun g := LinearMap.lsmul ℂ V (ZMod.stdAddChar (q * Multiplicative.toAdd g))
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_add, AddChar.map_add_eq_mul, smul_smul, mul_comm]
end Copies

section Fields
variable {F : Species → Type*} [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
def flavor (u : Species) : Representation ℂ (CyclicCharge.Group 4) (F u) := copies (fq u)
def scalarFlavor (u : BnvMixedInput.ScalarSpecies) :
    Representation ℂ (CyclicCharge.Group 4) (S u) := copies (bq u)

theorem field_scalar (g : CyclicCharge.Group 4) (u : Species)
    (x : DeltaLOneSignedFields.Field (F := F) u) :
    DeltaLOneSignedFields.field flavor u (1,g) x =
      MixedChargeSelection.cyclicCharacter g (fq u) • x := by
  have he : DeltaLOneSignedFields.field (flavor (F := F)) u (1,g) =
      MixedChargeSelection.cyclicCharacter g (fq u) • LinearMap.id := by
    apply TensorProduct.ext'
    intro v w
    simp [DeltaLOneSignedFields.field, ExternalInvariantTensor.external,
      Representation.tprod_apply, flavor, copies,
      MixedChargeSelection.cyclicCharacter, ← smul_eq_mul, TensorProduct.tmul_smul]
  exact LinearMap.congr_fun he x

theorem scalar_scalar (g : CyclicCharge.Group 4) (u : BnvMixedInput.ScalarSpecies)
    (x : BnvMixedInput.ScalarField (S := S) u) :
    BnvMixedInput.scalarField scalarFlavor u (1,g) x =
      MixedChargeSelection.cyclicCharacter g (bq u) • x := by
  have he : BnvMixedInput.scalarField (scalarFlavor (S := S)) u (1,g) =
      MixedChargeSelection.cyclicCharacter g (bq u) • LinearMap.id := by
    apply TensorProduct.ext'
    intro v w
    simp [BnvMixedInput.scalarField, ExternalInvariantTensor.external,
      Representation.tprod_apply, scalarFlavor, copies,
      MixedChargeSelection.cyclicCharacter, ← smul_eq_mul, TensorProduct.tmul_smul]
  exact LinearMap.congr_fun he x

theorem charge_of_nonzero {n m : ℕ}
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m)
    (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j))
    (hn : BnvMixedInput.value flavor scalarFlavor f p s v w ≠ 0) :
    (total p s : ZMod 4) = 0 := by
  apply (CyclicCharge.neutral_iff _).mp
  intro g
  have h := MixedWeightSupport.scalar_constraint
    (DeltaLOneSignedFields.fullRepresentation flavor) (BnvMixedInput.scalarRepresentation scalarFlavor)
    f (1,g) (fun i => Pi.single (p i) (v i)) (fun j => Pi.single (s j) (w j))
    (fun i => MixedChargeSelection.cyclicCharacter g (fq (p i)))
    (fun j => MixedChargeSelection.cyclicCharacter g (bq (s j)))
    (by
      intro i
      change FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field flavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, field_scalar]
      exact Pi.single_smul _ _ _)
    (by
      intro j
      change FiniteSpeciesExterior.representation (BnvMixedInput.scalarField scalarFlavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, scalar_scalar]
      exact Pi.single_smul _ _ _)
  have hz := (mul_eq_zero.mp h).resolve_right hn
  have ht := MixedChargeSelection.total_eq_character (MixedChargeSelection.cyclicCharacter g)
    (fun u => (fq u : ZMod 4)) (fun u => (bq u : ZMod 4)) p s
  have hc : MixedChargeSelection.charge (fun u => (fq u : ZMod 4))
      (fun u => (bq u : ZMod 4)) p s = (total p s : ZMod 4) := by
    simp [MixedChargeSelection.charge, total]
  rw [← hc]
  change MixedChargeSelection.cyclicCharacter g _ = 1
  rw [← ht]
  exact sub_eq_zero.mp hz

theorem nonneutral_b1 {b : ℤ} (hb : b.natAbs = 3) : (2*b : ZMod 4) ≠ 0 := by
  intro h
  have hd : (4 : ℤ) ∣ 2*b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp (by simpa using h)
  obtain ⟨k,hk⟩ := hd
  omega

def target (q : ℤ × ℤ) : Prop := q.1.natAbs = 3

theorem forbidden_values {n m : ℕ}
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m)
    (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j))
    (ht : (∑ i, baryon (p i)).natAbs = 3) :
    BnvMixedInput.value flavor scalarFlavor f p s v w = 0 := by
  by_contra hn
  have hc := charge_of_nonzero f p s v w hn
  rw [total_baryon] at hc
  exact nonneutral_b1 ht (by simpa using hc)

/-- All fermion and Higgs degrees on the actual SM/Higgs coefficient input. -/
theorem all_forbidden : ∀ n m,
    ∀ f : ComposableBLSupport.Input (flavor (F := F)) (scalarFlavor (S := S)) target n m, f = 0 := by
  intro n m f
  apply Subtype.ext
  apply BnvMixedInput.value_ext flavor scalarFlavor
  intro p s v w
  change BnvMixedInput.value flavor scalarFlavor f.val p s v w = 0
  by_cases h : ((ComposableBLSupport.specification target).test n m p s)
  · have ht : (∑ i, baryon (p i)).natAbs = 3 := by
      change target
        (MixedChargeSelection.charge ComposableBLSupport.fermionCharge ComposableBLSupport.bosonCharge p s) at h
      rw [ComposableBLSupport.charge_eq] at h
      exact h
    exact forbidden_values f.val p s v w ht
  · exact f.property p s h v w

theorem residual_forbidden (n m : ℕ)
    (q : ComposableBLSupport.Residual (flavor (F := F)) (scalarFlavor (S := S))
      target n m) : q = 0 := by
  let e := ComposableBLSupport.equiv (flavor (F := F)) (scalarFlavor (S := S))
    target n m
  calc
    q = e (e.symm q) := (e.apply_symm_apply q).symm
    _ = e 0 := congrArg e (all_forbidden n m (e.symm q))
    _ = 0 := e.map_zero

end Fields

section FullRelations
variable {U : Type*} [AddCommGroup U] [Module ℂ U]
  (P : DerivativeInterface.Input (CyclicCharge.Group 4) U)
  (V : Submodule ℂ U) (hV : ∀ g, V ≤ V.comap (P.action g))

/-- Selection retains the full stable relations, including degree-mixing EOM.
The charge law is on the selected raw source, never on a free approximation. -/
theorem derivative_selected_forbidden (b : ℤ) (hb : b.natAbs = 3)
    (hs : ∀ g (v : V), P.action g v.val =
      ZMod.stdAddChar ((2*(b : ZMod 4))*Multiplicative.toAdd g) • v.val) :
    DerivativeProhibition.Forbids (P.select V hV) := by
  obtain ⟨g,hg⟩ := (MixedChargeSelection.cyclic_detect_iff (2*(b : ZMod 4))).mpr
    (nonneutral_b1 hb)
  apply ((P.select V hV).forbidden_iff).mpr
  apply MixedScalarSelection.invariant_zero _ g
    (ZMod.stdAddChar ((2*(b : ZMod 4))*Multiplicative.toAdd g)) hg
  intro q
  apply DerivativeProhibition.quotient_scalar (P.select V hV) _ ?_ g q
  intro h v
  exact Subtype.ext (hs h v)

end FullRelations
end
end Physics.BaryonParitySelection
