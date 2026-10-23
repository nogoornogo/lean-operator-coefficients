import Physics.StandardModel.Operators.BaryonOne.Inputs.DeltaLOneSignedFields
import Math.RepresentationTheory.Weights.MixedWeightSupport
import Physics.FieldTheory.Spinor.Weyl.WeylCentralParity
import Math.RepresentationTheory.Content.MixedSpeciesExt

open Math

/-! Independent matter/Higgs input for bounded baryon violation.
Gauge and Weyl invariance are imposed on the whole mixed carrier, before any
family list is selected. Residual actions of both scalar species are explicit. -/
namespace Physics.BnvMixedInput
set_option autoImplicit false
noncomputable section
open Representation StandardSMGaugeTensor DeltaLOneSignedInput
open SMEpsilonTensor ExternalInvariantTensor
open scoped TensorProduct

abbrev ScalarSpecies := Fin 2
def ScalarGaugeCarrier : ScalarSpecies → Type
  | 0 => Weak
  | 1 => Module.Dual ℂ Weak
instance (s : ScalarSpecies) : AddCommGroup (ScalarGaugeCarrier s) := match s with
  | 0 => inferInstanceAs (AddCommGroup Weak)
  | 1 => inferInstanceAs (AddCommGroup (Module.Dual ℂ Weak))
instance (s : ScalarSpecies) : Module ℂ (ScalarGaugeCarrier s) := match s with
  | 0 => inferInstanceAs (Module ℂ Weak)
  | 1 => inferInstanceAs (Module ℂ (Module.Dual ℂ Weak))

def scalarGauge : (s : ScalarSpecies) → Representation ℂ GaugeGroup (ScalarGaugeCarrier s)
  | 0 => twist weak 3
  | 1 => (twist weak 3).dual

def scalarHypercharge : ScalarSpecies → ℤ := ![3,-3]

private theorem higgs_hypercharge (z : Circle) (x : Weak) :
    twist weak 3 (DeltaLOneSignedFields.hyperchargeElement z) x =
      (z : ℂ) ^ (3 : ℤ) • x := by
  simp [twist, phase, weak, DeltaLOneSignedFields.hyperchargeElement, Matrix.toLin'_one]
  rfl

theorem scalarGauge_hypercharge (z : Circle) (s : ScalarSpecies)
    (x : ScalarGaugeCarrier s) :
    scalarGauge s (DeltaLOneSignedFields.hyperchargeElement z) x =
      (z : ℂ) ^ scalarHypercharge s • x := by
  fin_cases s
  · exact higgs_hypercharge z x
  · change Module.Dual ℂ Weak at x
    change (twist weak 3).dual (DeltaLOneSignedFields.hyperchargeElement z) x =
      (z : ℂ) ^ (-3 : ℤ) • x
    apply LinearMap.ext
    intro v
    change x (twist weak 3 (DeltaLOneSignedFields.hyperchargeElement z)⁻¹ v) =
      (z : ℂ) ^ (-3 : ℤ) * x v
    have hi : (DeltaLOneSignedFields.hyperchargeElement z)⁻¹ =
        DeltaLOneSignedFields.hyperchargeElement z⁻¹ := by
      simp [DeltaLOneSignedFields.hyperchargeElement]
    rw [hi, higgs_hypercharge, map_smul, smul_eq_mul]
    simp

theorem scalarGauge_center (z : Circle) (hz : z ^ 3 = 1) (s : ScalarSpecies)
    (x : ScalarGaugeCarrier s) :
    scalarGauge s (DeltaLOneSignedFields.centerElement z hz) x = x := by
  have hweak (g : GaugeGroup) (hg : g.2 = 1) (v : Weak) : twist weak 3 g v = v := by
    simp [twist, phase, weak, hg, Matrix.toLin'_one]
  fin_cases s
  · exact hweak _ rfl x
  · change Module.Dual ℂ Weak at x
    change (twist weak 3).dual _ x = x
    apply LinearMap.ext; intro v
    change x (twist weak 3 (DeltaLOneSignedFields.centerElement z hz)⁻¹ v) = x v
    rw [hweak _ (by simp [DeltaLOneSignedFields.centerElement])]

variable {R : Type*} [Group R] {F : Species → Type*}
  [∀ s, AddCommGroup (F s)] [∀ s, Module ℂ (F s)]
  {S : ScalarSpecies → Type*} [∀ s, AddCommGroup (S s)] [∀ s, Module ℂ (S s)]
  (flavor : ∀ s, Representation ℂ R (F s))
  (scalarFlavor : ∀ s, Representation ℂ R (S s))

abbrev ScalarField (s : ScalarSpecies) := ScalarGaugeCarrier s ⊗[ℂ] S s

def scalarField (s : ScalarSpecies) :=
  external ((scalarGauge s).comp (MonoidHom.fst GaugeGroup WeylSpinor.Group))
    (scalarFlavor s)

def scalarRepresentation := FiniteSpeciesExterior.representation (scalarField scalarFlavor)

theorem scalarField_hypercharge (z : Circle) (s : ScalarSpecies)
    (x : ScalarField (S := S) s) :
    scalarField scalarFlavor s (DeltaLOneSignedFields.fullHypercharge z) x =
      (z : ℂ) ^ scalarHypercharge s • x := by
  have he : scalarField scalarFlavor s (DeltaLOneSignedFields.fullHypercharge z) =
      (z : ℂ) ^ scalarHypercharge s • LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    simp [scalarField, external, DeltaLOneSignedFields.fullHypercharge,
      Representation.tprod_apply, scalarGauge_hypercharge, TensorProduct.smul_tmul]
  rw [he]; rfl

theorem scalarField_center (z : Circle) (hz : z ^ 3 = 1) (s : ScalarSpecies)
    (x : ScalarField (S := S) s) :
    scalarField scalarFlavor s (DeltaLOneSignedFields.fullCenter z hz) x = x := by
  have he : scalarField scalarFlavor s (DeltaLOneSignedFields.fullCenter z hz) =
      LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    simp [scalarField, external, DeltaLOneSignedFields.fullCenter,
      Representation.tprod_apply, scalarGauge_center]
  rw [he]; rfl

abbrev Coefficient (n m : ℕ) := MixedWeightSupport.Coefficient
  (DeltaLOneSignedFields.fullRepresentation flavor) (scalarRepresentation scalarFlavor)
  (n := n) (m := m)

def value {n m : ℕ} (f : Coefficient flavor scalarFlavor n m)
    (fermions : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (fermions i))
    (w : ∀ j, ScalarField (S := S) (scalars j)) : ℂ :=
  f (MixedWeightSupport.pure (fun i => Pi.single (fermions i) (v i))
    (fun j => Pi.single (scalars j) (w j)))

theorem hypercharge_of_nonzero {n m : ℕ} (f : Coefficient flavor scalarFlavor n m)
    (fermions : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (fermions i))
    (w : ∀ j, ScalarField (S := S) (scalars j))
    (hf : value flavor scalarFlavor f fermions scalars v w ≠ 0) :
    (∑ i, hypercharge (fermions i)) + (∑ j, scalarHypercharge (scalars j)) = 0 := by
  apply MixedWeightSupport.circle_constraint
    (DeltaLOneSignedFields.fullRepresentation flavor) (scalarRepresentation scalarFlavor)
    f _ _ _ _ DeltaLOneSignedFields.fullHypercharge _ _ hf
  · intro z i
    change FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field flavor)
      (DeltaLOneSignedFields.fullHypercharge z) (Pi.single (fermions i) (v i)) =
      (z : ℂ) ^ hypercharge (fermions i) • Pi.single (fermions i) (v i)
    rw [FiniteSpeciesExterior.action_single, DeltaLOneSignedFields.field_hypercharge]
    exact Pi.single_smul _ _ _
  · intro z j
    change FiniteSpeciesExterior.representation (scalarField scalarFlavor)
      (DeltaLOneSignedFields.fullHypercharge z) (Pi.single (scalars j) (w j)) =
      (z : ℂ) ^ scalarHypercharge (scalars j) • Pi.single (scalars j) (w j)
    rw [FiniteSpeciesExterior.action_single, scalarField_hypercharge]
    exact Pi.single_smul _ _ _

theorem triality_of_nonzero {n m : ℕ} (f : Coefficient flavor scalarFlavor n m)
    (fermions : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (fermions i))
    (w : ∀ j, ScalarField (S := S) (scalars j))
    (hf : value flavor scalarFlavor f fermions scalars v w ≠ 0) :
    (∑ i, baryon (fermions i)) % 3 = 0 := by
  let z := DeltaLOneSignedFields.trialityRoot
  have hz := DeltaLOneSignedFields.trialityRoot_primitive
  have h := MixedWeightSupport.scalar_constraint
    (DeltaLOneSignedFields.fullRepresentation flavor) (scalarRepresentation scalarFlavor)
    f (DeltaLOneSignedFields.fullCenter z hz.pow_eq_one)
    (fun i => Pi.single (fermions i) (v i)) (fun j => Pi.single (scalars j) (w j))
    (fun i => (z : ℂ) ^ baryon (fermions i)) (fun _ => (1 : ℂ))
    (by
      intro i
      change FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field flavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, DeltaLOneSignedFields.field_center]
      exact Pi.single_smul _ _ _)
    (by
      intro j
      change FiniteSpeciesExterior.representation (scalarField scalarFlavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, scalarField_center, one_smul])
  simp only [Finset.prod_const_one, mul_one] at h
  rw [ExteriorWeightSupport.prod_zpow _ z.coe_ne_zero] at h
  have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hf)
  have hcircle : z ^ (∑ i, baryon (fermions i)) = 1 := by
    apply Subtype.ext
    exact he
  exact Int.emod_eq_zero_of_dvd ((hz.zpow_eq_one_iff_dvd _).mp hcircle)

def fullMinus : (GaugeGroup × WeylSpinor.Group) × R :=
  ((1, WeylCentralParity.minusIdentity), 1)

theorem field_minus (s : Species) (x : DeltaLOneSignedFields.Field (F := F) s) :
    DeltaLOneSignedFields.field flavor s fullMinus x = (-1 : ℂ) • x := by
  have he : DeltaLOneSignedFields.field flavor s fullMinus = (-1 : ℂ) • LinearMap.id := by
    apply TensorProduct.ext
    apply TensorProduct.ext
    apply LinearMap.ext; intro a
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro b
    change (DeltaLOneSignedFields.gauge s 1 a ⊗ₜ[ℂ]
      FourSameWeylCompleteness.action (DeltaLOneSignedFields.rightHanded s)
        WeylCentralParity.minusIdentity v) ⊗ₜ[ℂ] flavor s 1 b =
      (-1 : ℂ) • ((a ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] b)
    rw [WeylCentralParity.action_minus]
    simp only [map_one, Module.End.one_apply, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul]
  rw [he]; rfl

theorem scalarField_minus (s : ScalarSpecies) (x : ScalarField (S := S) s) :
    scalarField scalarFlavor s fullMinus x = x := by
  have he : scalarField scalarFlavor s fullMinus = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext; intro v
    apply LinearMap.ext; intro w
    simp [scalarField, external, fullMinus, Representation.tprod_apply]
  rw [he]; rfl

theorem even_fermions_of_nonzero {n m : ℕ} (f : Coefficient flavor scalarFlavor n m)
    (fermions : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (fermions i))
    (w : ∀ j, ScalarField (S := S) (scalars j))
    (hf : value flavor scalarFlavor f fermions scalars v w ≠ 0) : n % 2 = 0 := by
  have h := MixedWeightSupport.scalar_constraint
    (DeltaLOneSignedFields.fullRepresentation flavor) (scalarRepresentation scalarFlavor)
    f fullMinus (fun i => Pi.single (fermions i) (v i))
    (fun j => Pi.single (scalars j) (w j))
    (fun _ => (-1 : ℂ)) (fun _ => (1 : ℂ))
    (by
      intro i
      change FiniteSpeciesExterior.representation (DeltaLOneSignedFields.field flavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, field_minus]
      exact Pi.single_smul _ _ _)
    (by
      intro j
      change FiniteSpeciesExterior.representation (scalarField scalarFlavor) _ _ = _
      rw [FiniteSpeciesExterior.action_single, scalarField_minus, one_smul])
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_pow, mul_one] at h
  have he := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hf)
  exact Nat.even_iff.mp ((neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp he)

/-- Keep all nonzero baryon grades, without choosing a lepton grade or family. -/
def bnvSector (n m : ℕ) : Submodule ℂ (Coefficient flavor scalarFlavor n m) where
  carrier := {f | ∀ labels scalars v w, (∑ i, baryon (labels i)) = 0 →
    value flavor scalarFlavor f labels scalars v w = 0}
  zero_mem' := by
    intro labels scalars v w hb
    rfl
  add_mem' := by
    intro f h hf hh labels scalars v w hb
    change value flavor scalarFlavor f labels scalars v w +
      value flavor scalarFlavor h labels scalars v w = 0
    rw [hf labels scalars v w hb, hh labels scalars v w hb, add_zero]
  smul_mem' := by
    intro z f hf labels scalars v w hb
    change z * value flavor scalarFlavor f labels scalars v w = 0
    rw [hf labels scalars v w hb, mul_zero]

theorem degree_window (n m : ℕ) (hd : 3 * n + 2 * m ≤ 22) :
    n < 8 ∧ m < 12 := by omega

theorem baryon_sum_bounds {n : ℕ} (labels : Fin n → Species) :
    -(n : ℤ) ≤ (∑ i, baryon (labels i)) ∧ (∑ i, baryon (labels i)) ≤ n := by
  have hlow (s : Species) : (-1 : ℤ) ≤ baryon s := by fin_cases s <;> norm_num [baryon]
  have hupp (s : Species) : baryon s ≤ (1 : ℤ) := by fin_cases s <;> norm_num [baryon]
  constructor
  · simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlow (labels i))
  · simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hupp (labels i))

theorem bnv_minimum_dimension {n m : ℕ} (f : bnvSector flavor scalarFlavor n m)
    (fermions : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (fermions i))
    (w : ∀ j, ScalarField (S := S) (scalars j))
    (hf : value flavor scalarFlavor f.val fermions scalars v w ≠ 0) :
    4 ≤ n ∧ 12 ≤ 3 * n + 2 * m := by
  have hb : (∑ i, baryon (fermions i)) ≠ 0 := by
    intro hb
    exact hf (f.property fermions scalars v w hb)
  have ht := triality_of_nonzero flavor scalarFlavor f.val fermions scalars v w hf
  have hp := even_fermions_of_nonzero flavor scalarFlavor f.val fermions scalars v w hf
  have hs := baryon_sum_bounds fermions
  omega

theorem bnv_fermion_classes_le_eleven {n m : ℕ}
    (f : bnvSector flavor scalarFlavor n m) (hd : 3 * n + 2 * m ≤ 22)
    (fermions : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (fermions i))
    (w : ∀ j, ScalarField (S := S) (scalars j))
    (hf : value flavor scalarFlavor f.val fermions scalars v w ≠ 0) :
    (n = 4 ∧ m ≤ 5) ∨ (n = 6 ∧ m ≤ 2) := by
  have hs := bnv_minimum_dimension flavor scalarFlavor f fermions scalars v w hf
  have hp := even_fermions_of_nonzero flavor scalarFlavor f.val fermions scalars v w hf
  omega

theorem value_ext {n m : ℕ} (f h : Coefficient flavor scalarFlavor n m)
    (he : ∀ labels scalars v w,
      value flavor scalarFlavor f labels scalars v w =
        value flavor scalarFlavor h labels scalars v w) : f = h := by
  apply Representation.IntertwiningMap.ext
  exact MixedSpeciesExt.ext f.toLinearMap h.toLinearMap he

/-- Below the first mixed gate, no other fermion/scalar degree can contribute. -/
theorem bnv_degrees_le_seven {n m : ℕ}
    (f : bnvSector flavor scalarFlavor n m) (hd : 3 * n + 2 * m ≤ 14)
    (fermions : Fin n → Species) (scalars : Fin m → ScalarSpecies)
    (v : ∀ i, DeltaLOneSignedFields.Field (F := F) (fermions i))
    (w : ∀ j, ScalarField (S := S) (scalars j))
    (hf : value flavor scalarFlavor f.val fermions scalars v w ≠ 0) :
    n = 4 ∧ m ≤ 1 := by
  have hs := bnv_fermion_classes_le_eleven flavor scalarFlavor f
    (by omega) fermions scalars v w hf
  omega

theorem bnv_eq_zero_outside_seven_degrees {n m : ℕ}
    (f : bnvSector flavor scalarFlavor n m) (hd : 3 * n + 2 * m ≤ 14)
    (hout : n ≠ 4 ∨ 1 < m) : f = 0 := by
  apply Subtype.ext
  apply value_ext flavor scalarFlavor
  intro labels scalars v w
  change value flavor scalarFlavor f.val labels scalars v w = 0
  by_contra hf
  have hs := bnv_degrees_le_seven flavor scalarFlavor f hd labels scalars v w hf
  omega

theorem bnv_eq_zero_below_six {n m : ℕ}
    (f : bnvSector flavor scalarFlavor n m) (hd : 3 * n + 2 * m < 12) : f = 0 := by
  apply Subtype.ext
  apply value_ext flavor scalarFlavor
  intro labels scalars v w
  change value flavor scalarFlavor f.val labels scalars v w = 0
  by_contra hf
  have hs := bnv_minimum_dimension flavor scalarFlavor f labels scalars v w hf
  omega

set_option maxHeartbeats 800000 in
/-- Finite degree window is sufficient through eleven; out-of-bound entries
are required to be zero, not silently ignored by an expression generator. -/
def bounded (dimension : ℕ) : Submodule ℂ
    (∀ nm : Fin 8 × Fin 12, bnvSector flavor scalarFlavor nm.1.val nm.2.val) where
  carrier := {f | ∀ nm, 2 * dimension < 3 * nm.1.val + 2 * nm.2.val → f nm = 0}
  zero_mem' := by intro nm hd; rfl
  add_mem' := by
    intro f h hf hh nm hd
    change f nm + h nm = 0
    rw [hf nm hd, hh nm hd, add_zero]
  smul_mem' := by
    intro z f hf nm hd
    change z • f nm = 0
    rw [hf nm hd, smul_zero]

theorem bounded_eq_zero_below_six (dimension : ℕ) (hd : dimension < 6)
    (f : bounded flavor scalarFlavor dimension) : f = 0 := by
  apply Subtype.ext
  funext nm
  change f.val nm = 0
  by_cases hb : 2 * dimension < 3 * nm.1.val + 2 * nm.2.val
  · exact f.property nm hb
  · exact bnv_eq_zero_below_six flavor scalarFlavor (f.val nm) (by omega)

end
end Physics.BnvMixedInput
