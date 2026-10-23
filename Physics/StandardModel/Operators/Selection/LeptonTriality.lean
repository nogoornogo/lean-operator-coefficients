import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator
import Physics.StandardModel.Spectrum.Charges.FiniteChargeProfiles
import Physics.StandardModel.Gauge.Tensors.ResidualGaugeTensor
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

open Math

/-!
# Lepton triality without UV charge-orbit constraints

A nonempty three-generation target forbids all signatures in the existing
four-fermion predicate. The residual labels are actual characters of a finite
group. This is a spectrum-level counterexample, not yet a mass-radical source
construction or a statement about quantum anomalies and decay amplitudes.
-/

namespace Physics.LeptonTriality

noncomputable section

open StandardBranchProtonObstruction StandardAbelianCharge
open FiniteAbelianChargeSectors FiniteChargeProfiles StandardModelLocalOperator

/-- Left-handed charges; physical right-handed leptons have charge `q`. -/
def charges {A : Type*} [AddCommGroup A] (q : A) : Charges A :=
  ⟨0, 0, 0, q, -q⟩

@[simp] theorem protonFirst_charges {A : Type*} [AddCommGroup A] (q : A) :
    protonFirst (charges q) = q := by simp [charges, protonFirst]

@[simp] theorem protonSecond_charges {A : Type*} [AddCommGroup A] (q : A) :
    protonSecond (charges q) = q := by simp [charges, protonSecond]

theorem charges_not_orbitCompatible {A : Type*} [AddCommGroup A]
    (q : A) (hq : q ≠ 0) : ¬ SU5OrbitCompatible (charges q) := by
  intro h
  exact hq h.2.2.symm

theorem cyclic_charge_counterexample :
    protonFirst (charges (1 : ZMod 3)) ≠ 0 ∧
      protonSecond (charges (1 : ZMod 3)) ≠ 0 := by simp

/-- The group is multiplicative notation for the additive group of order three. -/
abbrev Residual := Multiplicative (ZMod 3)

def character : Residual →* Circle where
  toFun h := ZMod.toCircle h.toAdd
  map_one' := by simp
  map_mul' x y := by simp [AddChar.map_add_eq_mul]

theorem character_injective : Function.Injective character := by
  intro x y h
  exact Multiplicative.toAdd.injective (ZMod.injective_toCircle h)

theorem character_ne_one : character ≠ 1 := by
  intro h
  have he := congrArg (fun f : Residual →* Circle => f (Multiplicative.ofAdd 1)) h
  have hz : ZMod.toCircle (1 : ZMod 3) = ZMod.toCircle (0 : ZMod 3) := by
    simpa [character] using he
  have := ZMod.injective_toCircle hz
  exact one_ne_zero this

def label : ChargeLabel Residual := Additive.ofMul character

theorem label_ne_zero : label ≠ 0 := by
  intro h
  exact character_ne_one (congrArg Additive.toMul h)

theorem label_three_nsmul : (3 : ℕ) • label = 0 := by
  apply Additive.toMul.injective
  apply MonoidHom.ext
  intro x
  change (ZMod.toCircle x.toAdd) ^ 3 = 1
  rw [← AddChar.map_nsmul_eq_pow]
  simp only [nsmul_eq_mul]
  rw [ZMod.natCast_self, zero_mul]
  exact ZMod.toCircle.map_zero_eq_one

def assignment : Charges (ChargeLabel Residual) := charges label

theorem assignment_characters :
    protonFirstCharacter assignment = character ∧
      protonSecondCharacter assignment = character := by
  constructor
  · change (protonFirst (charges label)).toMul = character
    rw [protonFirst_charges]
    rfl
  · change (protonSecond (charges label)).toMul = character
    rw [protonSecond_charges]
    rfl

def family : Family (ChargeLabel Residual) :=
  ⟨pure 3 assignment, 3, by decide, pure_totals _ _⟩

def spectrum : ResolvedCharacter (ChargeLabel Residual) := target family.profiles

theorem spectrum_forgetting : forgetCharges spectrum = unchargedTarget 3 :=
  forgetCharges_target family.totals

theorem supported_iff (k : Charges (ChargeLabel Residual)) :
    ChargesSupported spectrum k ↔ k = assignment := by
  change ChargesSupported (target (pure 3 assignment)) k ↔ _
  rw [← occupied_iff_supported, occupied_pure_iff 3 (by decide)]

theorem assignment_supported : ChargesSupported spectrum assignment :=
  (supported_iff assignment).mpr rfl

theorem forbids_all_supported :
    ForbidsEverySupportedPhysicalDeltaBOneOperator spectrum := by
  apply forbidsEverySupportedStandardOperator_implies_physicalDeltaBOne
  intro k hk
  obtain rfl := (supported_iff k).mp hk
  apply (forbidsAllStandardOperators_iff assignment).mpr
  rw [assignment_characters.1, assignment_characters.2]
  exact ⟨character_ne_one, character_ne_one⟩

theorem spectrum_not_weylInvariant : ¬ ResolvedWeylInvariant spectrum := by
  intro h
  obtain ⟨k, hk, hc⟩ := exists_supported_su5OrbitCompatible spectrum h
    (fun hz => assignment_supported.1 (congrArg (fun f => f assignment.quark) hz))
    (fun hz => assignment_supported.2.2.1 (congrArg (fun f => f assignment.down) hz))
  obtain rfl := (supported_iff k).mp hk
  exact charges_not_orbitCompatible label label_ne_zero hc

/-- A positive family with real supported signatures, not vacuous prohibition. -/
theorem supported_spectrum_counterexample :
    family.generations = 3 ∧
      forgetCharges spectrum = unchargedTarget 3 ∧
      (∃ k, ChargesSupported spectrum k) ∧
      ForbidsEverySupportedPhysicalDeltaBOneOperator spectrum ∧
      ¬ ResolvedWeylInvariant spectrum :=
  ⟨rfl, spectrum_forgetting, ⟨assignment, assignment_supported⟩,
    forbids_all_supported, spectrum_not_weylInvariant⟩

/-- Positive common generation totals alone do not imply the no-go. -/
theorem not_universal_family_obstruction :
    ¬ ∀ F : Family (ChargeLabel Residual),
      ¬ ForbidsEverySupportedPhysicalDeltaBOneOperator (target F.profiles) := by
  intro h
  exact h family forbids_all_supported

/-- The actual canonical SM gauge tensors exist and transform nontrivially.
This is not an identification with a physical mass radical. -/
theorem canonical_tensors_not_invariant :
    StandardSMGaugeTensor.qque ≠ 0 ∧ StandardSMGaugeTensor.duql ≠ 0 ∧
      (¬ ∀ g x, StandardSMGaugeTensor.qque
        (StandardSMResidualTensor.qqueRepresentation assignment g x) =
          StandardSMGaugeTensor.qque x) ∧
      (¬ ∀ g x, StandardSMGaugeTensor.duql
        (StandardSMResidualTensor.duqlRepresentation assignment g x) =
          StandardSMGaugeTensor.duql x) := by
  refine ⟨StandardSMGaugeTensor.qque_nonzero, StandardSMGaugeTensor.duql_nonzero, ?_, ?_⟩
  · intro h
    exact character_ne_one (assignment_characters.1.symm.trans
      ((StandardSMResidualTensor.qque_invariant_iff assignment).mp h))
  · intro h
    exact character_ne_one (assignment_characters.2.symm.trans
      ((StandardSMResidualTensor.duql_invariant_iff assignment).mp h))

end

end Physics.LeptonTriality
