import Physics.StandardModel.Operators.ComposableBLSupport
import Math.RepresentationTheory.CyclicCharge

/-! Baryon-triality SM restriction. This reuses the BGW charge identity proof
with modulus three; the Higgs is charged. MSSM spectators are not in this alphabet. -/
namespace GUT.BaryonTrialitySMInput
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput
open scoped BigOperators TensorProduct

/-- Signed physical fields Q,uR,dR,L,eR and their opposites. -/
def fq : Species → ℤ := ![0,1,-1,2,1,0,-1,1,-2,-1]
def bq : BnvMixedInput.ScalarSpecies → ℤ := ![1,-1]

theorem fermion_identity (u : Species) :
    3 * fq u = hypercharge u - baryon u + 9 * lepton u := by
  fin_cases u <;> norm_num [fq, hypercharge, baryon, lepton]
theorem boson_identity (u : BnvMixedInput.ScalarSpecies) :
    3 * bq u = BnvMixedInput.scalarHypercharge u := by
  fin_cases u <;> norm_num [bq, BnvMixedInput.scalarHypercharge]

def total {n m : ℕ} (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies) : ℤ :=
  MixedChargeSelection.charge fq bq p s

theorem total_identity {n m : ℕ} (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies) :
    3 * total p s = ((∑ i, hypercharge (p i)) + ∑ j, BnvMixedInput.scalarHypercharge (s j)) -
      (∑ i, baryon (p i)) + 9 * (∑ i, lepton (p i)) := by
  simp only [total, MixedChargeSelection.charge, mul_add, Finset.mul_sum]
  simp_rw [fermion_identity, boson_identity]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

section Copies
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def copies (q : ZMod 3) : Representation ℂ (CyclicCharge.Group 3) V where
  toFun g := LinearMap.lsmul ℂ V (ZMod.stdAddChar (q * Multiplicative.toAdd g))
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [mul_add, AddChar.map_add_eq_mul, smul_smul, mul_comm]
end Copies

section Fields
variable {F : Species → Type*} [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]
def flavor (u : Species) : Representation ℂ (CyclicCharge.Group 3) (F u) := copies (fq u)
def scalarFlavor (u : BnvMixedInput.ScalarSpecies) :
    Representation ℂ (CyclicCharge.Group 3) (S u) := copies (bq u)

theorem field_scalar (g : CyclicCharge.Group 3) (u : Species)
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

theorem scalar_scalar (g : CyclicCharge.Group 3) (u : BnvMixedInput.ScalarSpecies)
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
    (total p s : ZMod 3) = 0 := by
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
    (fun u => (fq u : ZMod 3)) (fun u => (bq u : ZMod 3)) p s
  have hc : MixedChargeSelection.charge (fun u => (fq u : ZMod 3))
      (fun u => (bq u : ZMod 3)) p s = (total p s : ZMod 3) := by
    simp [MixedChargeSelection.charge, total]
  rw [← hc]
  change MixedChargeSelection.cyclicCharacter g _ = 1
  rw [← ht]
  exact sub_eq_zero.mp hz

theorem baryon_divisible {n m : ℕ}
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m)
    (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j))
    (hn : BnvMixedInput.value flavor scalarFlavor f p s v w ≠ 0) :
    (9 : ℤ) ∣ ∑ i, baryon (p i) := by
  have hy := BnvMixedInput.hypercharge_of_nonzero flavor scalarFlavor f p s v w hn
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd (total p s) 3).mp
    (charge_of_nonzero f p s v w hn)
  obtain ⟨k,hk⟩ := hc
  have ht := total_identity p s
  refine ⟨(∑ i, lepton (p i)) - k, ?_⟩
  rw [hy, hk] at ht
  norm_num at ht
  linarith

theorem forbidden_values {n m : ℕ}
    (f : BnvMixedInput.Coefficient flavor scalarFlavor n m)
    (p : Fin n → Species) (s : Fin m → BnvMixedInput.ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (p i))
    (w : ∀ j, BnvMixedInput.ScalarField (S := S) (s j))
    (target : (∑ i, baryon (p i)).natAbs = 3 ∨ (∑ i, baryon (p i)).natAbs = 6) :
    BnvMixedInput.value flavor scalarFlavor f p s v w = 0 := by
  by_contra hn
  obtain ⟨k,hk⟩ := baryon_divisible f p s v w hn
  omega

/-- The composed absolute B1/B2 specification on the actual SM/Higgs input. -/
theorem all_forbidden : ∀ n m,
    ∀ f : ComposableBLSupport.Input (flavor (F := F)) (scalarFlavor (S := S)) ComposableBLSupport.bOneTwo n m, f = 0 := by
  intro n m f
  apply Subtype.ext
  apply BnvMixedInput.value_ext flavor scalarFlavor
  intro p s v w
  change BnvMixedInput.value flavor scalarFlavor f.val p s v w = 0
  by_cases h : ((ComposableBLSupport.specification ComposableBLSupport.bOneTwo).test n m p s)
  · have ht : (∑ i, baryon (p i)).natAbs = 3 ∨ (∑ i, baryon (p i)).natAbs = 6 := by
      change ComposableBLSupport.bOneTwo
        (MixedChargeSelection.charge ComposableBLSupport.fermionCharge ComposableBLSupport.bosonCharge p s) at h
      rw [ComposableBLSupport.charge_eq] at h
      exact h
    exact forbidden_values f.val p s v w ht
  · exact f.property p s h v w

theorem residual_forbidden (n m : ℕ)
    (q : ComposableBLSupport.Residual (flavor (F := F)) (scalarFlavor (S := S))
      ComposableBLSupport.bOneTwo n m) : q = 0 := by
  let e := ComposableBLSupport.equiv (flavor (F := F)) (scalarFlavor (S := S))
    ComposableBLSupport.bOneTwo n m
  calc
    q = e (e.symm q) := (e.apply_symm_apply q).symm
    _ = e 0 := congrArg e (all_forbidden n m (e.symm q))
    _ = 0 := e.map_zero

end Fields

/-- DL(T) Eq.(2.17), n=0,p=m=1, physical right-handed conventions.
The entries are Q,uR,dR,L,eR,H_u,H_d. -/
theorem component_dictionary :
    (![fq 0,fq 1,fq 2,fq 3,fq 4,bq 0,bq 1] : Fin 7 → ZMod 3) =
      ![0,1,-1,-1,-2,1,-1] := by decide +kernel

end
end GUT.BaryonTrialitySMInput
