import Physics.StandardModel.Operators.BaryonTwo.Coefficients.DeltaBTwoSixQuark
import Lean.Util.CollectAxioms

/-! Persistent strict checks for the explicit all-right-handed six-quark pilot. -/

set_option autoImplicit false

namespace Physics.DeltaBTwoSixQuark.Audit

example : exteriorCoefficient (exteriorPower.ιMulti ℂ 6 witness) = 24 :=
  exteriorCoefficient_witness

example : exteriorCoefficient ≠ 0 := exteriorCoefficient_ne_zero

end Physics.DeltaBTwoSixQuark.Audit

run_cmd do
  let declarations := [
    ``Physics.DeltaBTwoSixQuark.colorAAS_tmul,
    ``Physics.DeltaBTwoSixQuark.orderedContraction_tmul,
    ``Physics.DeltaBTwoSixQuark.orderedContraction_invariant_linear,
    ``Physics.DeltaBTwoSixQuark.exteriorCoefficient,
    ``Physics.DeltaBTwoSixQuark.witness_evaluation,
    ``Physics.DeltaBTwoSixQuark.exteriorCoefficient_witness,
    ``Physics.DeltaBTwoSixQuark.exteriorCoefficient_ne_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B = 2 six-quark pilot: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B = 2 six-quark pilot: {declarations.length} strict transitive axiom checks passed"
