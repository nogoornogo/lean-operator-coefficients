import Math.RepresentationTheory.Content.MixedSpeciesPartition
import Math.RepresentationTheory.Symmetric.TypedPatternSymmetrization

/-! Strict audits of arbitrary mixed support and typed boson assembly. -/
open Lean in
run_cmd do
  let ds := [
    ``Math.SymmetricMultilinearProjection.project,
    ``Math.SymmetricMultilinearProjection.project_fixed,
    ``Math.MixedSpeciesProjection.cut_pure,
    ``Math.MixedSpeciesProjection.project_pure,
    ``Math.MixedSpeciesProjection.invariantProject,
    ``Math.MixedSpeciesProjection.project_mem,
    ``Math.MixedSpeciesProjection.project_eq_self,
    ``Math.MixedSpeciesProjection.projectLinear,
    ``Math.MixedSpeciesPartition.split_join,
    ``Math.MixedSpeciesPartition.join_split,
    ``Math.MixedSpeciesPartition.equiv,
    ``Math.TypedPatternSymmetrization.symmetric_pure,
    ``Math.TypedPatternSymmetrization.symmetric_vanish]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Mixed species partition {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Mixed species partition: {ds.length} strict transitive checks passed"
