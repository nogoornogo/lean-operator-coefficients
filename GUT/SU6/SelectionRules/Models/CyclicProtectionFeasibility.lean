import GUT.SU6.SelectionRules.Models.PhysicalIndexObstruction
import Physics.StandardModel.Operators.Selection.InverseCyclicSMCharges

/-! Structural admission test for universal neutral-Higgs cyclic SM inputs.
The target is an actual radical index; no representation/copy cutoff or
computed branching/rank table is a premise. -/
namespace GUT.SU6ProtectionFeasibility
set_option autoImplicit false
noncomputable section
open Math Physics Representation
open FiniteChargeProfiles FiniteAbelianChargeSectors StandardBranchProtonObstruction
open InvariantWeylMass UnitaryVirtualRealization

variable {k : ℕ} [NeZero k]

/-- Genuine residual characters for an arbitrary positive cyclic order. -/
def cyclicLabel (q : ZMod k) : ChargeLabel (CyclicCharge.Group k) :=
  Additive.ofMul {
    toFun := fun g => ZMod.toCircle (q * Multiplicative.toAdd g)
    map_one' := by simp
    map_mul' := by intro g h; simp [mul_add, AddChar.map_add_eq_mul] }

theorem cyclicLabel_injective : Function.Injective (cyclicLabel (k := k)) := by
  intro a b he
  have h := congrArg (fun c : ChargeLabel (CyclicCharge.Group k) =>
    c.toMul (Multiplicative.ofAdd (1 : ZMod k))) he
  apply ZMod.injective_toCircle
  simpa [cyclicLabel] using h

/-- The index characters and the existing infrared scalar actions use the
same phase, rather than merely identically named arithmetic labels. -/
theorem cyclicLabel_scalar_action (q : ZMod k) (g : CyclicCharge.Group k) (x : ℂ) :
    CyclicCharge.representation q g x = ((cyclicLabel q).toMul g : ℂ) * x := rfl

/-- All-left order Q, uc, dc, L, ec for a Higgs of residual charge h. -/
def yukawaCharges (q l h : ZMod k) : Charges (ChargeLabel (CyclicCharge.Group k)) :=
  ⟨cyclicLabel q, cyclicLabel (-q-h), cyclicLabel (-q+h),
    cyclicLabel l, cyclicLabel (-l+h)⟩

/-- The neutral-Higgs specialization used by the existing actual IR iff. -/
def charges (q l : ZMod k) : Charges (ChargeLabel (CyclicCharge.Group k)) :=
  yukawaCharges q l 0

/-- The existing actual three-generation, four-family bounded B1 input. -/
abbrev LightSector (q l : ZMod k) :=
  DeltaLOneSignedFields.Sector
    (FlavoredCyclicSelection.flavor (fun _ : Fin 5 => Fin 3)
      (InverseCyclicSMCharges.universal q l)) 1

variable
  (R : ActualUnitaryGroupRepresentation
    (ChargedAmbientRealization.AmbientGroup (CyclicCharge.Group k)))
  (B : SymmetricMass (SU6.PhysicalChainSource.physicalFields R).rho)

/-- A Higgs charge alone cannot repair the pure-target index obstruction.
The Higgs charge cancels between the two derived character equalities. -/
theorem target_forces_yukawa_neutral (q l h : ZMod k) (N : ℕ) (hN : 0 < N)
    (s : ChargeLabel (CyclicCharge.Group k) →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (yukawaCharges q l h)) s) : 3*q+l = 0 := by
  obtain ⟨hu,he⟩ := SU6PhysicalIndexObstruction.pure_charge_equalities
    R B N hN (yukawaCharges q l h) s ht
  have hU : q = -q-h := cyclicLabel_injective hu
  have hE : q = -l+h := cyclicLabel_injective he
  linear_combination hU + hE

/-- The actual SU(6) pure-target condition forces the bounded B1 charge to zero. -/
theorem target_forces_neutral (q l : ZMod k) (N : ℕ) (hN : 0 < N)
    (s : ChargeLabel (CyclicCharge.Group k) →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (charges q l)) s) : 3*q+l = 0 :=
  target_forces_yukawa_neutral R B q l 0 N hN s ht

/-- A charge-protecting input cannot supply this actual SU(6) radical index. -/
theorem no_target_of_nonzero_charge (q l : ZMod k) (N : ℕ) (hN : 0 < N)
    (s : ChargeLabel (CyclicCharge.Group k) →₀ ℤ) (h : 3*q+l ≠ 0) :
    ¬ ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (charges q l)) s :=
  fun ht => h (target_forces_neutral R B q l N hN s ht)

/-- The associated three-generation SM input has an actual allowed coefficient.
This is not a construction of an actual UV-to-light field equivalence. -/
theorem light_allowed_of_target (q l : ZMod k) (N : ℕ) (hN : 0 < N)
    (s : ChargeLabel (CyclicCharge.Group k) →₀ ℤ)
    (ht : ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (charges q l)) s) : SelectionCriteria.Allowed (LightSector q l) :=
  (InverseCyclicSMCharges.three_generation_allowed_iff q l).mpr
    (target_forces_neutral R B q l N hN s ht)

/-- The actual bounded prohibition predicate, rather than a charge-only test,
is incompatible with every positive pure target in this class. -/
theorem no_target_of_light_forbidden (q l : ZMod k) (N : ℕ) (hN : 0 < N)
    (s : ChargeLabel (CyclicCharge.Group k) →₀ ℤ)
    (hp : SelectionCriteria.Forbidden (LightSector q l)) :
    ¬ ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (charges q l)) s :=
  no_target_of_nonzero_charge R B q l N hN s
    ((InverseCyclicSMCharges.three_generation_forbidden_iff q l).mp hp)

/-- The unconstrained neutral infrared input is allowed, not declared forbidden. -/
theorem neutral_light_allowed : SelectionCriteria.Allowed (LightSector (0 : ZMod k) 0) :=
  (InverseCyclicSMCharges.three_generation_allowed_iff 0 0).mpr (by simp)

/-- Concrete lepton-parity failure of the proposed commuting SU(6) lift. -/
theorem lepton_parity_no_target
    (R : ActualUnitaryGroupRepresentation
      (ChargedAmbientRealization.AmbientGroup (CyclicCharge.Group 2)))
    (B : SymmetricMass (SU6.PhysicalChainSource.physicalFields R).rho)
    (N : ℕ) (hN : 0 < N) (s : ChargeLabel (CyclicCharge.Group 2) →₀ ℤ) :
    ¬ ProfileZeroModeSupport.HasTarget (SU6.PhysicalChainSource.physicalFields R) B
      (pure N (charges (0 : ZMod 2) 1)) s :=
  no_target_of_nonzero_charge R B 0 1 N hN s (by norm_num)

end
end GUT.SU6ProtectionFeasibility
