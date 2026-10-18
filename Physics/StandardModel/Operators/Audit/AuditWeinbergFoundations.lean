import Math.RepresentationTheory.MixedSquareDescent
import Physics.FieldTheory.Spinor.WeylPairInvariant
import Physics.StandardModel.Gauge.WeinbergWeakInvariant
import Lean.Util.CollectAxioms

open Math

/-! Strict transitive audits for mixed statistics and the local Weinberg invariant lines. -/
run_cmd do
  let declarations := [
    ``Math.MixedSquareDescent.orderedEquiv,
    ``Math.MixedSquareDescent.lift_apply,
    ``Math.MixedSquareDescent.equivariantEquiv,
    ``GUT.WeylPairInvariant.coordinateEquiv,
    ``GUT.WeylPairInvariant.nonzero_iff,
    ``GUT.WeinbergWeakInvariant.coordinateEquiv,
    ``GUT.WeinbergWeakInvariant.contraction_apply,
    ``GUT.WeinbergWeakInvariant.diagonal_apply]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weinberg foundations: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weinberg foundations: {declarations.length} strict transitive axiom checks passed"
