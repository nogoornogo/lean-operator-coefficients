import Math.LinearAlgebra.MajoranaUnitaryClassification
import Lean.Util.CollectAxioms

/-! Strict transitive audit of the full-unitary matrix criterion and controls. -/
run_cmd do
  let declarations := [
    ``Math.UnitaryDiagonalCongruence.bilinear_iff,
    ``Math.UnitaryDiagonalCongruence.preserves_iff,
    ``Math.UnitaryDiagonalCongruence.entry_iff,
    ``Math.UnitaryDiagonalCongruence.subgroup,
    ``Math.UnitaryDiagonalCongruence.no_mixing,
    ``Math.UnitaryDiagonalCongruence.nonnegative_iff,
    ``Math.UnitaryDiagonalCongruence.zero_subgroup,
    ``Math.UnitaryDiagonalCongruence.constant_iff,
    ``Math.UnitaryDiagonalCongruence.orthogonalHom_bijective,
    ``Math.UnitaryDiagonalCongruence.constantEquiv,
    ``Math.UnitaryMajoranaBlocks.decomposition,
    ``Math.UnitaryMajoranaBlocks.unitaryAssemble,
    ``Math.UnitaryMajoranaBlocks.assemble_bijective,
    ``Math.UnitaryMajoranaBlocks.productEquiv,
    ``Math.MajoranaPhaseNormalization.exists_phase,
    ``Math.MajoranaPhaseNormalization.phase_spec,
    ``Math.MajoranaPhaseNormalization.phase_zero,
    ``Math.MajoranaPhaseNormalization.diagonalPhase_spec,
    ``Math.MajoranaPhaseNormalization.undo_congruence,
    ``Math.MajoranaPhaseNormalization.conjugate_preserves,
    ``Math.MajoranaPhaseNormalization.congruenceEquiv,
    ``Math.MajoranaPhaseNormalization.normalizationEquiv,
    ``Math.MajoranaUnitaryClassification.reindexEquiv,
    ``Math.MajoranaUnitaryClassification.indexEquiv,
    ``Math.MajoranaUnitaryClassification.mass_normSq_injective,
    ``Math.MajoranaUnitaryClassification.localClassification,
    ``Math.MajoranaUnitaryClassification.zeroEquiv,
    ``Math.MajoranaUnitaryClassification.splitEquiv,
    ``Math.MajoranaUnitaryClassification.classification,
    ``Math.MajoranaUnitaryClassification.residualHomEquiv,
    ``Math.MajoranaUnitaryClassification.residual_nonzero_iff,
    ``Math.MajoranaUnitaryClassification.opposite_phase_mixing]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo m!"Unitary diagonal congruence: {declarations.length} strict transitive checks passed"
