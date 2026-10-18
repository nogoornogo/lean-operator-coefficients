import Physics.StandardModel.Operators.ComposableBLSupport
import Math.RepresentationTheory.CyclicCharge

/-! A sufficient finite subgroup of Koren's three-generation SM symmetry. -/
namespace GUT.KorenSMSelection
set_option autoImplicit false
noncomputable section
open Math Representation DeltaLOneSignedInput

abbrev H := CyclicCharge.Group 9 × CyclicCharge.Group 3

def embedding : H →* Circle × CyclicCharge.Group 3 where
  toFun g := (ZMod.toCircle (Multiplicative.toAdd g.1), g.2)
  map_one' := by simp
  map_mul' g h := by simp [AddChar.map_add_eq_mul]

theorem embedding_injective : Function.Injective embedding := by
  intro g h he
  have h1 := ZMod.injective_toCircle (congrArg Prod.fst he)
  have h2 := congrArg Prod.snd he
  exact Prod.ext (congrArg Multiplicative.ofAdd h1) h2

def chi (g : H) : AddChar (ℤ × ℤ) ℂ where
  toFun q := ZMod.stdAddChar (((q.1 - 3*q.2 : ℤ) : ZMod 9) * Multiplicative.toAdd g.1) *
    ZMod.stdAddChar ((q.2 : ZMod 3) * Multiplicative.toAdd g.2)
  map_zero_eq_one' := by simp
  map_add_eq_mul' q r := by
    change ZMod.stdAddChar (((q.1+r.1-3*(q.2+r.2) : ℤ) : ZMod 9) * _) *
      ZMod.stdAddChar (((q.2+r.2 : ℤ) : ZMod 3) * _) = _
    have he : q.1+r.1-3*(q.2+r.2) = (q.1-3*q.2)+(r.1-3*r.2) := by ring
    rw [he]
    simp only [Int.cast_add, add_mul, AddChar.map_add_eq_mul]
    ring

/-- The finite action is the restriction of the paper's continuous/discrete weights. -/
theorem chi_restriction (g : H) (q : ℤ × ℤ) :
    chi g q = MixedChargeSelection.circleCharacter (embedding g).1 (q.1-3*q.2) *
      MixedChargeSelection.cyclicCharacter (embedding g).2 (q.2 : ZMod 3) := by
  change ZMod.stdAddChar (((q.1-3*q.2 : ℤ) : ZMod 9) * Multiplicative.toAdd g.1) * _ =
    ((ZMod.toCircle (Multiplicative.toAdd g.1) : Circle) : ℂ) ^ (q.1-3*q.2) * _
  congr 1
  change ZMod.stdAddChar (((q.1-3*q.2 : ℤ) : ZMod 9) * Multiplicative.toAdd g.1) =
    (ZMod.stdAddChar (Multiplicative.toAdd g.1)) ^ (q.1-3*q.2)
  simpa [zsmul_eq_mul] using
    (ZMod.stdAddChar (N := 9)).map_zsmul_eq_zpow (q.1-3*q.2) (Multiplicative.toAdd g.1)

theorem chi_mul (g h : H) (q : ℤ × ℤ) : chi (g*h) q = chi g q * chi h q := by
  simp [chi, mul_add, AddChar.map_add_eq_mul]
  ring

def target (q : ℤ × ℤ) : Prop := q.1.natAbs = 3 ∨ q.1.natAbs = 6 ∨ q.2.natAbs = 2

theorem target_union : ComposableBLSupport.specification target =
    ProhibitionSpecification.union
      (ComposableBLSupport.specification (fun q => q.1.natAbs = 3))
      (ProhibitionSpecification.union
        (ComposableBLSupport.specification (fun q => q.1.natAbs = 6))
        (ComposableBLSupport.specification (fun q => q.2.natAbs = 2))) := rfl

theorem neutral_iff (q : ℤ × ℤ) :
    (∀ g : H, chi g q = 1) ↔ (9 : ℤ) ∣ q.1 - 3*q.2 ∧ (3 : ℤ) ∣ q.2 := by
  constructor
  · intro h
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mp
      apply (CyclicCharge.neutral_iff _).mp
      intro g
      simpa [chi] using h (g,1)
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      apply (CyclicCharge.neutral_iff _).mp
      intro g
      simpa [chi] using h (1,g)
  · rintro ⟨hb,hl⟩ g
    have hb' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 9).mpr hb
    have hl' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr hl
    change ZMod.stdAddChar (((q.1-3*q.2 : ℤ) : ZMod 9) * _) *
      ZMod.stdAddChar ((q.2 : ZMod 3) * _) = 1
    rw [hb', hl']
    simp

theorem baryon_divisible (q : ℤ × ℤ) (h : ∀ g : H, chi g q = 1) : (9 : ℤ) ∣ q.1 := by
  obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := (neutral_iff q).mp h
  refine ⟨a+b, ?_⟩
  linarith

theorem detect (q : ℤ × ℤ) (ht : target q) : ∃ g : H, chi g q ≠ 1 := by
  by_contra hn
  have h : ∀ g : H, chi g q = 1 := by simpa using hn
  obtain ⟨a,ha⟩ := baryon_divisible q h
  obtain ⟨b,hb⟩ := ((neutral_iff q).mp h).2
  unfold target at ht
  omega

section Fields
variable {F : Species → Type*} [∀ u, AddCommGroup (F u)] [∀ u, Module ℂ (F u)]
  {S : BnvMixedInput.ScalarSpecies → Type*}
  [∀ u, AddCommGroup (S u)] [∀ u, Module ℂ (S u)]

def copies {V : Type*} [AddCommGroup V] [Module ℂ V] (q : ℤ × ℤ) : Representation ℂ H V where
  toFun g := LinearMap.lsmul ℂ V (chi g q)
  map_one' := by ext; simp [chi]
  map_mul' g h := by ext; simp [chi_mul, smul_smul, mul_comm]

def flavor (u : Species) : Representation ℂ H (F u) := copies (ComposableBLSupport.fermionCharge u)
def scalarFlavor (u : BnvMixedInput.ScalarSpecies) : Representation ℂ H (S u) :=
  copies (ComposableBLSupport.bosonCharge u)

theorem all_forbidden : ∀ n m,
    ∀ f : ComposableBLSupport.Input (flavor (F := F)) (scalarFlavor (S := S)) target n m, f = 0 := by
  apply ComposableBLSupport.forbidden _ _ target chi
  · intro g u v; rfl
  · intro g u v; rfl
  · intro n m p s ht; exact detect _ ht

theorem residual_forbidden (n m : ℕ)
    (q : ComposableBLSupport.Residual (flavor (F := F)) (scalarFlavor (S := S)) target n m) : q = 0 := by
  let e := ComposableBLSupport.equiv (flavor (F := F)) (scalarFlavor (S := S)) target n m
  calc
    q = e (e.symm q) := (e.apply_symm_apply q).symm
    _ = e 0 := congrArg e (all_forbidden n m (e.symm q))
    _ = 0 := e.map_zero
end Fields

theorem printed_dictionary :
    ComposableBLSupport.fermionCharge 0 = (1,0) ∧
    ComposableBLSupport.fermionCharge 6 = (-1,0) ∧
    ComposableBLSupport.fermionCharge 7 = (-1,0) ∧
    ComposableBLSupport.fermionCharge 3 = (0,1) ∧
    ComposableBLSupport.fermionCharge 9 = (0,-1) := by decide

theorem fermion_conjugates (i : Fin 5) :
    ComposableBLSupport.fermionCharge ⟨i.val+5, by omega⟩ =
      -ComposableBLSupport.fermionCharge ⟨i.val, by omega⟩ := by
  fin_cases i <;> decide

theorem higgs_neutral (u : BnvMixedInput.ScalarSpecies) (g : H) :
    chi g (ComposableBLSupport.bosonCharge u) = 1 := by simp [chi, ComposableBLSupport.bosonCharge]

theorem llhh_detect : ∃ g : H, chi g (0,2) ≠ 1 := detect _ (Or.inr (Or.inr rfl))
end
end GUT.KorenSMSelection
