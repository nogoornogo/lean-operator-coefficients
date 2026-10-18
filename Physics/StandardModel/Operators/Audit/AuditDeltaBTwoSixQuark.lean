import Physics.StandardModel.Operators.DeltaBTwoSixQuark
import Lean.Util.CollectAxioms

/-! Persistent strict checks for the explicit all-right-handed six-quark pilot. -/

set_option autoImplicit false

namespace GUT.DeltaBTwoSixQuark.Audit

example : exteriorCoefficient (exteriorPower.ιMulti ℂ 6 witness) = 24 :=
  exteriorCoefficient_witness

example : exteriorCoefficient ≠ 0 := exteriorCoefficient_ne_zero

end GUT.DeltaBTwoSixQuark.Audit

run_cmd do
  let declarations := [
    ``GUT.DeltaBTwoSixQuark.colorAAS_tmul,
    ``GUT.DeltaBTwoSixQuark.orderedContraction_tmul,
    ``GUT.DeltaBTwoSixQuark.orderedContraction_invariant_linear,
    ``GUT.DeltaBTwoSixQuark.exteriorCoefficient,
    ``GUT.DeltaBTwoSixQuark.witness_evaluation,
    ``GUT.DeltaBTwoSixQuark.exteriorCoefficient_witness,
    ``GUT.DeltaBTwoSixQuark.exteriorCoefficient_ne_zero]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Delta-B = 2 six-quark pilot: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Delta-B = 2 six-quark pilot: {declarations.length} strict transitive axiom checks passed"
