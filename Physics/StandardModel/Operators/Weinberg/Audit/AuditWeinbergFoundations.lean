import Math.RepresentationTheory.Constructions.MixedSquareDescent
import Physics.FieldTheory.Spinor.Tensors.WeylPairInvariant
import Physics.StandardModel.Gauge.Tensors.WeinbergWeakInvariant
import Lean.Util.CollectAxioms

open Math

/-! Strict transitive audits for mixed statistics and the local Weinberg invariant lines. -/
run_cmd do
  let declarations := [
    ``Math.MixedSquareDescent.orderedEquiv,
    ``Math.MixedSquareDescent.lift_apply,
    ``Math.MixedSquareDescent.equivariantEquiv,
    ``Physics.WeylPairInvariant.coordinateEquiv,
    ``Physics.WeylPairInvariant.nonzero_iff,
    ``Physics.WeinbergWeakInvariant.coordinateEquiv,
    ``Physics.WeinbergWeakInvariant.contraction_apply,
    ``Physics.WeinbergWeakInvariant.diagonal_apply]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Weinberg foundations: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Weinberg foundations: {declarations.length} strict transitive axiom checks passed"
