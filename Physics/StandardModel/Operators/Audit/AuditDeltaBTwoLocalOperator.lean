import Physics.StandardModel.Operators.DeltaBTwoLocalOperator
import Lean.Util.CollectAxioms

/-! Persistent strict checks for the Delta-B = 2 grading pilot. -/

set_option autoImplicit false

namespace GUT.DeltaBTwoLocalOperator.Audit

open StandardBranchProtonObstruction

example : IsDimensionNineDeltaBTwo udduddOperator :=
  uddudd_isDimensionNineDeltaBTwo

example : IsAllRightHandedGaugeNeutralSixQuark udduddOperator :=
  uddudd_isAllRightHandedGaugeNeutralSixQuark

example {A : Type*} [AddCommGroup A] (k : Charges A) :
    operatorCharge k udduddOperator = -(2 • k.up + 4 • k.down) := by
  simpa [udduddCharge] using uddudd_operatorCharge k

end GUT.DeltaBTwoLocalOperator.Audit

run_cmd do
  let declarations := [
    ``GUT.DeltaBTwoLocalOperator.uddudd_quantumNumbers,
    ``GUT.DeltaBTwoLocalOperator.uddudd_isDimensionNineDeltaBTwo,
    ``GUT.DeltaBTwoLocalOperator.uddudd_isAllRightHandedGaugeNeutralSixQuark,
    ``GUT.DeltaBTwoLocalOperator.uddudd_baryonGrade,
    ``GUT.DeltaBTwoLocalOperator.uddudd_operatorCharge,
    ``GUT.DeltaBTwoLocalOperator.residualProhibits_iff_charge_ne_zero,
    ``GUT.DeltaBTwoLocalOperator.uddudd_residualProhibits_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B = 2 grading: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B = 2 grading: {declarations.length} strict transitive axiom checks passed"
