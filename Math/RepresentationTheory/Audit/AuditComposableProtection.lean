import Math.Audit.ImportOrigin
import Math.RepresentationTheory.ProhibitionSpecification
import Math.RepresentationTheory.ComposableProtection
import Math.LinearAlgebra.CoefficientSelectorComposition
import Math.RepresentationTheory.ComposableProtectionExamples

open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`Physics).isPrefixOf mod || (`GUT).isPrefixOf mod then
      throwError "Composable protection imports forbidden layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Math.ProhibitionSpecification.Spec,
    ``Math.ProhibitionSpecification.pullback,
    ``Math.ProhibitionSpecification.empty,
    ``Math.ProhibitionSpecification.full,
    ``Math.ProhibitionSpecification.union,
    ``Math.ProhibitionSpecification.inter,
    ``Math.ProhibitionSpecification.compl,
    ``Math.ProhibitionSpecification.iUnion,
    ``Math.ProhibitionSpecification.charges,
    ``Math.ProhibitionSpecification.Satisfies,
    ``Math.ProhibitionSpecification.union_iff,
    ``Math.ProhibitionSpecification.iUnion_iff,
    ``Math.ProhibitionSpecification.mono,
    ``Math.ProhibitionSpecification.inter_of_left,
    ``Math.ProhibitionSpecification.empty_satisfies,
    ``Math.ProhibitionSpecification.all_union_iff,
    ``Math.ComposableProtection.forbidden_iff,
    ``Math.ComposableProtection.protected_iff,
    ``Math.ComposableProtection.forbidden_union_iff,
    ``Math.ComposableProtection.protected_union_iff,
    ``Math.ComposableProtection.all_forbidden_union_iff,
    ``Math.ComposableProtection.all_protected_union_iff,
    ``Math.ComposableProtection.charges_forbidden,
    ``Math.CoefficientSelectorComposition.combine,
    ``Math.CoefficientSelectorComposition.combine_zero_iff,
    ``Math.CoefficientSelectorComposition.transport_zero_iff,
    ``Math.CoefficientSelectorComposition.restriction_square,
    ``Math.CoefficientSelectorComposition.intersection_not_union,
    ``Math.ComposableProtectionExamples.overlapping,
    ``Math.ComposableProtectionExamples.selected_phase,
    ``Math.ComposableProtectionExamples.neutral_local]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Composable protection {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Composable protection: {ds.length} strict transitive checks passed"
