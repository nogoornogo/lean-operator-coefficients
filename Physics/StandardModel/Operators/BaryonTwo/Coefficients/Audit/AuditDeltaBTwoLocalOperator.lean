import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoLocalOperator
import Lean.Util.CollectAxioms

/-! Persistent strict checks for the Delta-B = 2 grading pilot. -/

set_option autoImplicit false

namespace Physics.DeltaBTwoLocalOperator.Audit

open StandardBranchProtonObstruction

example : IsDimensionNineDeltaBTwo udduddOperator :=
  uddudd_isDimensionNineDeltaBTwo

example : IsAllRightHandedGaugeNeutralSixQuark udduddOperator :=
  uddudd_isAllRightHandedGaugeNeutralSixQuark

example {A : Type*} [AddCommGroup A] (k : Charges A) :
    operatorCharge k udduddOperator = -(2 • k.up + 4 • k.down) := by
  simpa [udduddCharge] using uddudd_operatorCharge k

end Physics.DeltaBTwoLocalOperator.Audit

run_cmd do
  let declarations := [
    ``Physics.DeltaBTwoLocalOperator.uddudd_quantumNumbers,
    ``Physics.DeltaBTwoLocalOperator.uddudd_isDimensionNineDeltaBTwo,
    ``Physics.DeltaBTwoLocalOperator.uddudd_isAllRightHandedGaugeNeutralSixQuark,
    ``Physics.DeltaBTwoLocalOperator.uddudd_baryonGrade,
    ``Physics.DeltaBTwoLocalOperator.uddudd_operatorCharge,
    ``Physics.DeltaBTwoLocalOperator.residualProhibits_iff_charge_ne_zero,
    ``Physics.DeltaBTwoLocalOperator.uddudd_residualProhibits_iff]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B = 2 grading: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B = 2 grading: {declarations.length} strict transitive axiom checks passed"
