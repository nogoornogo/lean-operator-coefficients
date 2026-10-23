import Math.RepresentationTheory.Coefficients.FiniteLocalRelationCompleteness
import Math.RepresentationTheory.Relations.SignedRelationControls
import Lean.Util.CollectAxioms

/-! Strict transitive audit of quotient completeness and sign controls. -/
run_cmd do
  let declarations := [
    ``Math.RelationQuotient.equiv,
    ``Math.RelationQuotient.equiv_mk,
    ``Math.RelationQuotient.equiv_symm_apply,
    ``Math.RelationQuotient.vanish_relations_iff,
    ``Math.RelationQuotient.relations_stable,
    ``Math.SignedRelationQuotient.equiv,
    ``Math.SignedRelationQuotient.empty_relations,
    ``Math.SignedRelationQuotient.identity_relations,
    ``Math.SignedRelationQuotient.identity_relations_top,
    ``Math.ResidualRelationPresentation.familyEquiv,
    ``Math.ResidualRelationPresentation.stable,
    ``Math.ResidualRelationPresentation.equiv,
    ``Math.ResidualRelationPresentation.equiv_single,
    ``Math.FiniteLocalRelationCompleteness.equiv,
    ``Math.FiniteLocalRelationCompleteness.extraction,
    ``Math.FiniteLocalRelationCompleteness.reconstruction,
    ``Math.FiniteLocalRelationCompleteness.nonzero_iff,
    ``Math.SignedRelationControls.boson_admissible,
    ``Math.SignedRelationControls.fermion_admissible,
    ``Math.SignedRelationControls.boson_not_fermion,
    ``Math.SignedRelationControls.fermion_not_boson,
    ``Math.SignedRelationControls.bosonDescended_nonzero,
    ``Math.SignedRelationControls.fermionDescended_nonzero,
    ``Math.SignedRelationControls.incompatible_identity_quotient]
  for decl in declarations do
    for ax in (← Lean.collectAxioms decl) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Relation completeness: {decl} uses unexpected axiom {ax}"
  Lean.logInfo m!"Relation completeness: {declarations.length} strict transitive checks passed"
