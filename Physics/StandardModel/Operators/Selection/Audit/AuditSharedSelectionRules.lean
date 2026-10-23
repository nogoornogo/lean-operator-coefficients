import Math.Audit.ImportOrigin
import Physics.StandardModel.Gauge.Tensors.ResidualGaugeTensor
import Physics.StandardModel.Operators.Selection.StandardModelLocalOperator
import Mathlib.Algebra.Ring.Int.Units

open Math

/-! Persistent tensor audit, including a genuinely nontrivial finite charge
and a negative selection-rule test. These are tests of standard field spaces,
not assertions about an arbitrary physical mass radical. -/

set_option autoImplicit false

-- Check the actual transitive environment, not just the direct imports.
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "Shared selection-rule audit imports SU(6): {mod}"

namespace Physics.AuditStandardSMGaugeTensor

noncomputable section

open StandardSMGaugeTensor StandardSMResidualTensor
open StandardBranchProtonObstruction FiniteAbelianChargeSectors

def sign : ℤˣ →* Circle where
  toFun u := ⟨((u : ℤ) : ℂ), by
    obtain rfl | rfl := Int.units_eq_one_or u <;>
      norm_num [Submonoid.unitSphere]⟩
  map_one' := Subtype.ext (by norm_num)
  map_mul' u v := Subtype.ext (by
    change (((u * v : ℤˣ) : ℤ) : ℂ) = ((u : ℤ) : ℂ) * ((v : ℤ) : ℂ)
    simp)

@[simp] theorem sign_coe (u : ℤˣ) : (sign u : ℂ) = ((u : ℤ) : ℂ) := rfl

def allowedCharges : Charges (ChargeLabel ℤˣ) where
  quark := Additive.ofMul sign
  up := Additive.ofMul sign
  down := 0
  lepton := 0
  electron := Additive.ofMul sign

theorem allowed_characters :
    protonFirstCharacter allowedCharges = 1 ∧ protonSecondCharacter allowedCharges = 1 := by
  constructor <;> apply MonoidHom.ext <;> intro u <;>
    simp [allowedCharges, protonFirstCharacter_apply, protonSecondCharacter_apply]

theorem allowed_nonzero_tensors :
    qque ≠ 0 ∧ duql ≠ 0 ∧
      (∀ g x, qque (StandardSMResidualTensor.qqueRepresentation allowedCharges g x) = qque x) ∧
      (∀ g x, duql (StandardSMResidualTensor.duqlRepresentation allowedCharges g x) = duql x) :=
  invariant_tensors_of_su5OrbitCompatible allowedCharges ⟨rfl, rfl, rfl⟩

/-- A deliberately non-standard charge-orbit bridge-compatible assignment must not be reported invariant. -/
def forbiddenCharges : Charges (ChargeLabel ℤˣ) where
  quark := 0
  up := Additive.ofMul sign
  down := 0
  lepton := 0
  electron := 0

theorem forbidden_qque_witness :
    qque (StandardSMResidualTensor.qqueRepresentation forbiddenCharges (1, -1) qqueWitness) = -1 := by
  rw [qque_covariant]
  norm_num [forbiddenCharges, protonFirstCharacter_apply]

theorem forbidden_duql_witness :
    duql (StandardSMResidualTensor.duqlRepresentation forbiddenCharges (1, -1) duqlWitness) = -1 := by
  rw [duql_covariant]
  norm_num [forbiddenCharges, protonSecondCharacter_apply]

theorem forbidden_qque_not_invariant :
    ¬ ∀ g x, qque (StandardSMResidualTensor.qqueRepresentation forbiddenCharges g x) = qque x := by
  intro h
  have he := h (1, -1) qqueWitness
  rw [forbidden_qque_witness, qque_witness] at he
  norm_num at he

theorem forbidden_duql_not_invariant :
    ¬ ∀ g x, duql (StandardSMResidualTensor.duqlRepresentation forbiddenCharges g x) = duql x := by
  intro h
  have he := h (1, -1) duqlWitness
  rw [forbidden_duql_witness, duql_witness] at he
  norm_num at he

#print axioms SMEpsilonTensor.eps2_invariant
#print axioms SMEpsilonTensor.eps3_invariant
#print axioms StandardSMGaugeTensor.qqueIntertwiner
#print axioms StandardSMGaugeTensor.duqlIntertwiner
#print axioms StandardSMGaugeTensor.qque_nonzero
#print axioms StandardSMGaugeTensor.duql_nonzero
#print axioms qqueRepresentation_eq
#print axioms duqlRepresentation_eq
#print axioms qque_invariant_iff
#print axioms duql_invariant_iff
#print axioms allowed_nonzero_tensors
#print axioms forbidden_qque_not_invariant
#print axioms forbidden_duql_not_invariant

end

end Physics.AuditStandardSMGaugeTensor

namespace Physics.AuditSharedSelectionRules

open StandardAbelianCharge StandardModelLocalOperator
open FiniteAbelianChargeSectors AuditStandardSMGaugeTensor

noncomputable section

example : Finite ℤˣ := inferInstance

theorem sign_nontrivial : sign (-1) ≠ 1 := by
  intro h
  have he := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at he

/-- The raw determinant direction disappears from the rank-four normal form. -/
theorem diagonal_shift_not_distinguished :
    (fun _ : Fin 5 => (1 : ℤ)) ≠ (0 : RawWeight) ∧
      normalizeWeight (fun _ => 1) = normalizeWeight 0 := by
  constructor
  · intro h
    have he := congrFun h 0
    norm_num at he
  · ext i
    simp [normalizeWeight]

/-- Independent residual labels are not discarded with the determinant direction. -/
theorem residual_sign_distinguished :
    ((0 : ReducedWeight), Additive.ofMul sign) ≠
      ((0 : ReducedWeight), (0 : ChargeLabel ℤˣ)) := by
  intro h
  have he := congrArg (fun k : ResolvedKey (ChargeLabel ℤˣ) => k.2.toMul (-1)) h
  exact sign_nontrivial he

theorem operator_hypercharge_convention :
    sixHypercharge .quarkDoublet = 1 ∧ sixHypercharge .upRight = 4 ∧
      sixHypercharge .downRight = -2 ∧ sixHypercharge .leptonDoublet = -3 ∧
      sixHypercharge .electronRight = -6 := ⟨rfl, rfl, rfl, rfl, rfl⟩

#print axioms StandardAbelianCharge.normalizeWeight_eq_iff
#print axioms StandardAbelianCharge.normalizeWeight_surjective
#print axioms StandardAbelianCharge.exists_supported_neutral_proton_sectors
#print axioms protonCharacters_eq_one_of_su5OrbitCompatible
#print axioms StandardSMResidualTensor.invariant_tensors_of_su5OrbitCompatible
#print axioms sign_nontrivial
#print axioms diagonal_shift_not_distinguished
#print axioms residual_sign_distinguished
#print axioms operator_hypercharge_convention
#print axioms StandardModelLocalOperator.qque_isPhysicalDeltaBOneOperator
#print axioms StandardModelLocalOperator.duql_isPhysicalDeltaBOneOperator

end

end Physics.AuditSharedSelectionRules
