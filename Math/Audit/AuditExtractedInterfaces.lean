import Math.LinearAlgebra.EigenbasisTrace
import Math.RepresentationTheory.Characters.VirtualRepresentation
import Math.RepresentationTheory.Decomposition.Schur
import Math.RepresentationTheory.Unitary.ContinuousConstructions
import Math.RepresentationTheory.Unitary.HaarAveraging
import Lean.Util.CollectAxioms

/-! Persistent axiom checks for generic interfaces extracted from mixed
application modules. Names and statements remain the existing public API. -/

run_cmd do
  let declarations := [
    ``Math.CompactEmbeddingClassification.IsUnitaryRepresentation,
    ``Math.CompactEmbeddingClassification.orthogonalSubrepresentation,
    ``Math.CompactEmbeddingClassification.isCompl_orthogonalSubrepresentation,
    ``Math.CompactEmbeddingClassification.isSemisimpleRepresentation_of_unitary,
    ``Math.ContinuousRepresentationScope.IsJointlyContinuous,
    ``Math.ContinuousRepresentationScope.IsJointlyContinuous.orbit,
    ``Math.ContinuousRepresentationScope.IsJointlyContinuous.operator,
    ``Math.ContinuousRepresentationScope.IsJointlyContinuous.subrepresentation,
    ``Math.ContinuousRepresentationScope.IsJointlyContinuous.comp,
    ``Math.ContinuousRepresentationScope.IsContinuousFiniteDimensionalIrrep,
    ``Math.PhysicalRestrictionBridge.ActualGroupRepresentation.character,
    ``Math.PhysicalRestrictionBridge.VirtualGroupSummand.character,
    ``Math.PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.character,
    ``Math.PhysicalRestrictionBridge.FiniteVirtualGroupRepresentation.CharacterEquivalent,
    ``Math.BlockCentralizer.intertwiningMap_eq_zero_of_finrank_ne,
    ``Math.BlockCentralizer.intertwiningMap_eq_smul_one_of_irreducible,
    ``Math.BlockCentralizer.comp_isIrreducible_of_surjective,
    ``Math.WeightTheory.trace_eq_sum_of_basis_eigen,
    ``Math.ContinuousUnitaryConstructions.jointlyContinuous_of_orbit,
    ``Math.ContinuousUnitaryConstructions.basisCopyRepresentationEquiv,
    ``Math.ContinuousUnitaryConstructions.basisCopyRepresentation_jointlyContinuous,
    ``Math.ContinuousUnitaryConstructions.jointlyContinuous_tprod,
    ``Math.ContinuousUnitaryConstructions.unitary_tprod,
    ``Math.CompactRepresentationUnitarization.averagedInner_re_pos,
    ``Math.CompactRepresentationUnitarization.averagedInnerCore,
    ``Math.CompactRepresentationUnitarization.averagedInner_invariant]
  for decl in declarations do
    let axioms ← Lean.collectAxioms decl
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Extracted interface {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Extracted interfaces: {declarations.length} strict transitive axiom checks passed"
