import GUT.SU6.SelectionRules.StandardBranch.StandardSMRadicalTensor
import GUT.SU6.SelectionRules.Audit.AuditStandardSMGaugeTensor

open Math

/-! Persistent full-gauge mass/radical audit. The benchmark is constructed
without an assumed radical dimension, operator support, or nonzero tensor.
Its neutral analytic SU(6) lift is audited separately in
`AuditStandardSMUVMass`. -/

set_option autoImplicit false

namespace GUT.AuditStandardSMRadicalTensor

noncomputable section

open StandardSMFullGaugeMass StandardSMRadicalTensor
open AuditStandardSMGaugeTensor FiniteAbelianChargeSectors

theorem actual_mass_radical_benchmark :
    Module.finrank ℂ Fields = 27 ∧ (mass allowedCharges).form ≠ 0 ∧
      Module.finrank ℂ (ZeroModes allowedCharges) = 15 ∧
      qque allowedCharges ≠ 0 ∧ duql allowedCharges ≠ 0 ∧
      (∀ g x, qque allowedCharges (qqueRho allowedCharges g x) = qque allowedCharges x) ∧
      (∀ g x, duql allowedCharges (duqlRho allowedCharges g x) = duql allowedCharges x) := by
  refine ⟨fields_finrank, mass_nonzero _, radical_finrank _, qque_nonzero _, duql_nonzero _, ?_, ?_⟩
  · intro g x
    rw [qque_covariant, allowed_characters.1]
    simp
  · intro g x
    rw [duql_covariant, allowed_characters.2]
    simp

theorem forbidden_qque_on_radical :
    qque forbiddenCharges
      (qqueRho forbiddenCharges (1, -1)
        ((qqueSplit forbiddenCharges).embed StandardSMGaugeTensor.qqueWitness)) = -1 := by
  rw [qque_covariant, qque_witness]
  norm_num [forbiddenCharges, protonFirstCharacter_apply]

theorem forbidden_duql_on_radical :
    duql forbiddenCharges
      (duqlRho forbiddenCharges (1, -1)
        ((duqlSplit forbiddenCharges).embed StandardSMGaugeTensor.duqlWitness)) = -1 := by
  rw [duql_covariant, duql_witness]
  norm_num [forbiddenCharges, protonSecondCharacter_apply]

#print axioms SplitWeylMass.mem_radical_iff
#print axioms SplitWeylMass.radicalEquiv
#print axioms SplitWeylMass.radical_character
#print axioms SplitRepresentationProjection.dualMap
#print axioms SplitRepresentationProjection.bidualEquiv
#print axioms SplitRepresentationProjection.Split.tensor
#print axioms SplitRepresentationProjection.Split.pullback_nonzero
#print axioms StandardSMFullGaugeMass.mass
#print axioms StandardSMFullGaugeMass.radicalEquiv
#print axioms StandardSMFullGaugeMass.mass_nonzero
#print axioms StandardSMFullGaugeMass.radical_finrank
#print axioms StandardSMRadicalTensor.upSplit
#print axioms StandardSMRadicalTensor.qqueIntertwiner
#print axioms StandardSMRadicalTensor.duqlIntertwiner
#print axioms StandardSMRadicalTensor.qque_nonzero
#print axioms StandardSMRadicalTensor.duql_nonzero
#print axioms StandardSMRadicalTensor.source_benchmark
#print axioms actual_mass_radical_benchmark
#print axioms forbidden_qque_on_radical
#print axioms forbidden_duql_on_radical

end

end GUT.AuditStandardSMRadicalTensor
