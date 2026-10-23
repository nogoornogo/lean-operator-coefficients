import Math.Audit.ImportOrigin
import Physics.FieldTheory.Jets.Weyl.Equations.WeylSingleFieldIBP
import Physics.FieldTheory.Jets.Weyl.Equations.ConjugateWeylEquation
import Physics.FieldTheory.Jets.Weyl.Equations.WeylJetAdjoint

/-! Strict transitive standard-axiom and import-layer audit. -/
open Lean in
run_cmd do
  let env ← getEnv
  for mod in env.header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "Unexpected source layer {mod}; original {SourceLayout.originalModule mod}"
  let ds := [
    ``Physics.WeylSingleFieldIBP.Source,
    ``Physics.WeylSingleFieldIBP.Relations,
    ``Physics.WeylSingleFieldIBP.Quotient,
    ``Physics.WeylSingleFieldIBP.action,
    ``Physics.WeylSingleFieldIBP.relations_top,
    ``Physics.WeylSingleFieldIBP.quotient_zero,
    ``Physics.WeylSingleFieldIBP.dimension,
    ``Physics.WeylSingleFieldIBP.basis,
    ``Physics.WeylSingleFieldIBP.coefficient_zero,
    ``Physics.WeylSingleFieldIBP.firstJet,
    ``Physics.WeylSingleFieldIBP.firstJet_nonzero,
    ``Physics.WeylSingleFieldIBP.firstJet_ibp_zero,
    ``Physics.ConjugateWeylEquation.equationConjugation,
    ``Physics.ConjugateWeylEquation.equationConjugation_apply,
    ``Physics.ConjugateWeylEquation.equationConjugation_involutive,
    ``Physics.ConjugateWeylEquation.spinor_conjugation,
    ``Physics.ConjugateWeylEquation.field_conjugation,
    ``Physics.ConjugateWeylEquation.direction_real,
    ``Physics.ConjugateWeylEquation.jet_conjugation,
    ``Physics.ConjugateWeylEquation.equation_action,
    ``Physics.ConjugateWeylEquation.rightSeed,
    ``Physics.ConjugateWeylEquation.rightSeed_covariant,
    ``Physics.ConjugateWeylEquation.equationConjugation_row,
    ``Physics.ConjugateWeylEquation.rightSeed_row_zero,
    ``Physics.ConjugateWeylEquation.rightSeed_row_one,
    ``Physics.ConjugateWeylEquation.rightRelations,
    ``Physics.ConjugateWeylEquation.RightGenerator,
    ``Physics.ConjugateWeylEquation.rightAction,
    ``Physics.ConjugateWeylEquation.conjugate_relations,
    ``Physics.ConjugateWeylEquation.conjugate_right_relations,
    ``Physics.ConjugateWeylEquation.conjugate_relations_iff,
    ``Physics.ConjugateWeylEquation.toRight,
    ``Physics.ConjugateWeylEquation.toLeft,
    ``Physics.ConjugateWeylEquation.toLeft_toRight,
    ``Physics.ConjugateWeylEquation.toRight_toLeft,
    ``Physics.ConjugateWeylEquation.toRight_shift,
    ``Physics.ConjugateWeylEquation.toLeft_shift,
    ``Physics.ConjugateWeylEquation.toRight_action,
    ``Physics.ConjugateWeylEquation.toLeft_action,
    ``Physics.ConjugateWeylEquation.right_higher_jet_survives,
    ``Physics.WeylJetAdjoint.Paired,
    ``Physics.WeylJetAdjoint.Algebra,
    ``Physics.WeylJetAdjoint.conjugation,
    ``Physics.WeylJetAdjoint.conjugation_involutive,
    ``Physics.WeylJetAdjoint.shift,
    ``Physics.WeylJetAdjoint.conjugation_shift,
    ``Physics.WeylJetAdjoint.shift_commute,
    ``Physics.WeylJetAdjoint.action,
    ``Physics.WeylJetAdjoint.conjugation_action,
    ``Physics.WeylJetAdjoint.adjoint,
    ``Physics.WeylJetAdjoint.adjoint_generator,
    ``Physics.WeylJetAdjoint.adjoint_mul,
    ``Physics.WeylJetAdjoint.adjoint_involutive,
    ``Physics.WeylJetAdjoint.derivative,
    ``Physics.WeylJetAdjoint.adjoint_derivative,
    ``Physics.WeylJetAdjoint.derivative_commute,
    ``Physics.WeylJetAdjoint.adjoint_action,
    ``Physics.WeylJetAdjoint.IBP,
    ``Physics.WeylJetAdjoint.Source,
    ``Physics.WeylJetAdjoint.adjoint_ibp,
    ``Physics.WeylJetAdjoint.sourceAdjoint,
    ``Physics.WeylJetAdjoint.sourceAdjoint_mk,
    ``Physics.WeylJetAdjoint.sourceAdjoint_involutive,
    ``Physics.WeylJetAdjoint.rawConjugation,
    ``Physics.WeylJetAdjoint.projection,
    ``Physics.WeylJetAdjoint.projection_surjective,
    ``Physics.WeylJetAdjoint.projection_conjugation,
    ``Physics.WeylJetAdjoint.algebraProjection,
    ``Physics.WeylJetAdjoint.algebraProjection_surjective,
    ``Physics.WeylJetAdjoint.algebraProjection_adjoint,
    ``Physics.WeylJetAdjoint.left_descendant_zero,
    ``Physics.WeylJetAdjoint.right_descendant_zero]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Declaration {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"Jet EOM completion: {ds.length} strict transitive checks passed"
