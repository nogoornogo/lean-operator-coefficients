import Math.Audit.ImportOrigin
import GUT.SU5.SelectionRules.SelectionRule
import GUT.SU5.Audit.AuditMatterSource
import Physics.StandardModel.Operators.Selection.Audit.AuditSharedSelectionRules

open Physics

open Math

/-! Final scope controls. In particular the zero-generation universal
prohibition is vacuous, and a finite odd character has genuine field support. -/

set_option autoImplicit false

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    let mod := SourceLayout.originalModule mod
    if (`GUT.SU6).isPrefixOf mod then
      throwError "SU(5) endpoint audit imports SU(6): {mod}"

namespace GUT.SU5.AuditSelectionRule

noncomputable section

open MatterSource ResidualSectors SupportedFields SupportedTensors SupportedQuotient SelectionRule
open StandardModelEmbedding StandardSMGaugeTensor StandardModelLocalOperator
open StandardBranchProtonObstruction FiniteAbelianChargeSectors AuditMatterSource

variable {H : Type*} [CommGroup H]

theorem no_realization_zero {W : Type*} [AddCommGroup W] [Module ℂ W] [Nontrivial W]
    {sigma : Representation ℂ GaugeGroup W} {chi : H →* Circle}
    {R : OrdinaryAction H 0} (F : Realization R sigma chi) : False := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne W
  exact hxy (F.injective (Subsingleton.elim _ _))

theorem no_field_zero (R : OrdinaryAction H 0) (k : Charges (ChargeLabel H)) (f : PhysicalFermion) :
    ¬ FieldSupported R k f := by
  let : Nontrivial Quark := Module.nontrivial_of_finrank_pos (R := ℂ) (by
    simp [Quark, Module.finrank_tensorProduct, SMEpsilonTensor.Color, SMEpsilonTensor.Weak])
  cases f <;> rintro ⟨F⟩ <;> exact no_realization_zero F

theorem zero_vacuously_forbids (R : OrdinaryAction H 0) : ForbidsEverySupportedDeltaBOne R := by
  intro ks O _ hs
  exact (no_field_zero R (ks 0) (O 0) (hs 0)).elim

theorem one_generation_nonvacuous :
    ∃ M : Model H, M.generations = 1 ∧ ¬ ForbidsEverySupportedDeltaBOne M.residual ∧
      Nonempty (OperatorWitness M.residual) :=
  ⟨oneGeneration H, rfl, oneGeneration_result H⟩

def finiteOddMode : Mode mixingSource .ten where
  character := oddCharacter
  vector := WithLp.toLp 2 ![1, -1]
  nonzero := by intro h; have he := congrArg (fun v : Generations 2 => v 0) h; norm_num at he
  eigen := odd_mode

def finiteTrivialMode : Mode mixingSource .barFive where
  character := 1
  vector := WithLp.toLp 2 ![1, 0]
  nonzero := by intro h; have he := congrArg (fun v : Generations 2 => v 0) h; norm_num at he
  eigen := by
    have hv : WithLp.toLp 2 (![1, 0] : Fin 2 → ℂ) ∈ sector mixingSource .barFive 1 := by
      rw [repeated_barFive_character]
      trivial
    exact hv

def finiteFields := support finiteOddMode finiteTrivialMode

def finiteEvenMode : Mode mixingSource .ten where
  character := 1
  vector := WithLp.toLp 2 ![1, 1]
  nonzero := by intro h; have he := congrArg (fun v : Generations 2 => v 0) h; norm_num at he
  eigen := even_mode

/-- The first Q is even, while the other Q, u^c and e^c are odd. -/
def mixedSlotCharges (s : Fin 4) : Charges (ChargeLabel ℤˣ) :=
  if s = 0 then charges finiteEvenMode finiteTrivialMode else charges finiteOddMode finiteTrivialMode

theorem mixed_slots_supported : SlotsSupported mixingSource mixedSlotCharges qqueOperator := by
  intro s
  by_cases hs : s = 0
  · simpa [mixedSlotCharges, hs] using
      support_fields (support finiteEvenMode finiteTrivialMode) (qqueOperator s)
  · simpa [mixedSlotCharges, hs] using support_fields finiteFields (qqueOperator s)

theorem mixed_slots_not_neutral : slotCharacter mixedSlotCharges qqueOperator ≠ 1 := by
  have hsum : (∑ s, physicalCharge (mixedSlotCharges s) (qqueOperator s)) =
      (0 : ChargeLabel ℤˣ) + Additive.ofMul oddCharacter +
        -Additive.ofMul oddCharacter + -Additive.ofMul oddCharacter := by
    rw [Fin.sum_univ_four]
    rfl
  have hc : slotCharacter mixedSlotCharges qqueOperator = oddCharacter⁻¹ := by
    unfold slotCharacter
    rw [hsum]
    simp
  intro h
  rw [hc] at h
  have he := congrArg (fun c : ℤˣ →* Circle => (c (-1) : ℂ)) h
  norm_num [oddCharacter] at he

theorem finite_odd_character_nontrivial : oddCharacter ≠ 1 := by
  intro h
  have he := congrArg (fun c : ℤˣ →* Circle => (c (-1) : ℂ)) h
  norm_num [oddCharacter] at he

theorem finite_odd_charge_torsion :
    (Additive.ofMul oddCharacter : ChargeLabel ℤˣ) + Additive.ofMul oddCharacter = 0 := by
  change oddCharacter * oddCharacter = 1
  ext h
  rcases Int.units_eq_one_or h with rfl | rfl <;> simp [oddCharacter]

theorem finite_odd_supported_neutral :
    OperatorSupported mixingSource (charges finiteOddMode finiteTrivialMode) qqueOperator ∧
      operatorCharacter (charges finiteOddMode finiteTrivialMode) qqueOperator = 1 := by
  refine ⟨support_operator finiteFields _, ?_⟩
  rw [qque_operatorCharacter]
  exact (protonCharacters_eq_one_of_su5OrbitCompatible _
    (charges_compatible finiteOddMode finiteTrivialMode)).1

theorem finite_odd_quotient_tensors :
    qqueTensor finiteFields ≠ 0 ∧ duqlTensor finiteFields ≠ 0 ∧
      (∀ g x, qqueTensor finiteFields (quotientQQueAction finiteFields g x) = qqueTensor finiteFields x) ∧
      (∀ g x, duqlTensor finiteFields (quotientDuqlAction finiteFields g x) = duqlTensor finiteFields x) :=
  ⟨qqueTensor_nonzero _, duqlTensor_nonzero _,
    qque_quotient_invariant _ (charges_compatible _ _),
    duql_quotient_invariant _ (charges_compatible _ _)⟩

theorem finite_mixing_endpoint :
    ¬ ForbidsEverySupportedDeltaBOne mixingSource ∧ Nonempty (OperatorWitness mixingSource) :=
  scoped_no_go mixingSource (by decide)

theorem sign_kernel_invisible {n : ℕ} {R : OrdinaryAction H n} {k : Charges (ChargeLabel H)}
    (S : Support R k) : qqueAction S (signKernelElement, 1) = 1 ∧
      duqlAction S (signKernelElement, 1) = 1 := by
  have hg : (signKernelElement, (1 : H)) ∈ (coverQuotient (H := H)).ker :=
    (mem_coverQuotient_ker _).mpr ⟨hom_signKernelElement, rfl⟩
  exact ⟨qque_kernel S hg, duql_kernel S hg⟩

/-- The dual character must be inverted even away from order-two phases. -/
def quarterTurn : Circle := ⟨Complex.I, by norm_num [Submonoid.unitSphere]⟩

theorem inverse_character_not_same :
    (((MonoidHom.id Circle)⁻¹) quarterTurn : ℂ) = -Complex.I ∧
      (((MonoidHom.id Circle)⁻¹) quarterTurn : ℂ) ≠ ((MonoidHom.id Circle) quarterTurn : ℂ) := by
  constructor
  · change Complex.I⁻¹ = -Complex.I
    exact Complex.inv_I
  · change Complex.I⁻¹ ≠ Complex.I
    rw [Complex.inv_I]
    intro he
    have him := congrArg Complex.im he
    norm_num at him

theorem charged_dual_quarter_turn (phi : Module.Dual ℂ SMEpsilonTensor.Color) :
    (StandardSMResidualTensor.charged upRight (MonoidHom.id Circle)).dual
      (1, quarterTurn) phi = (-Complex.I) • phi := by
  ext x
  simp [Representation.dual, StandardSMResidualTensor.charged, quarterTurn, map_smul]

/-- Preserve the negative IR controls: neutrality is not asserted for an
arbitrary assignment that has no compatible commuting UV source. -/
theorem incompatible_IR_tensor_rejected :
    ¬ ∀ g x, StandardSMGaugeTensor.qque
      (StandardSMResidualTensor.qqueRepresentation AuditStandardSMGaugeTensor.forbiddenCharges g x) =
        StandardSMGaugeTensor.qque x :=
  AuditStandardSMGaugeTensor.forbidden_qque_not_invariant

#print axioms RepresentationDescent.descend_comp
#print axioms RepresentationDescent.descend_invariant
#print axioms field_kernel
#print axioms fieldAction_cover
#print axioms fieldAction_val
#print axioms qque_kernel
#print axioms duql_kernel
#print axioms quotientQQueAction_cover
#print axioms quotientDuqlAction_cover
#print axioms qque_quotient_invariant
#print axioms duql_quotient_invariant
#print axioms witness_exists
#print axioms scoped_no_go
#print axioms Model.selection_rule_obstruction
#print axioms oneGeneration_result
#print axioms zero_vacuously_forbids
#print axioms one_generation_nonvacuous
#print axioms finite_odd_character_nontrivial
#print axioms finite_odd_charge_torsion
#print axioms finite_odd_supported_neutral
#print axioms mixed_slots_supported
#print axioms mixed_slots_not_neutral
#print axioms finite_odd_quotient_tensors
#print axioms finite_mixing_endpoint
#print axioms sign_kernel_invisible
#print axioms inverse_character_not_same
#print axioms charged_dual_quarter_turn
#print axioms incompatible_IR_tensor_rejected

end

end GUT.SU5.AuditSelectionRule
