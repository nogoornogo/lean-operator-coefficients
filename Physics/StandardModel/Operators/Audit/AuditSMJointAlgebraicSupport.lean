import Physics.StandardModel.Operators.SMJointColoredSupport
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

/-! Optional symbolic character consumers. The independent structural audit
continues to reject evaluator imports. This audit permits generic character
correctness but rejects retired closed numerical certificate modules. -/
run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "joint occurrence audit imports {mod}; original {SourceLayout.originalModule mod}"
    for numerical in [`Physics.StandardModel.Operators.SMConstantContentRanks,
        `Physics.StandardModel.Operators.LLHHKernelRank,
        `Physics.StandardModel.Operators.SMNeutralCertificates,
        `Physics.StandardModel.Operators.SMNeutralSparseExamples,
        `Physics.StandardModel.Operators.SMComputableCharacterExamples] do
      if numerical.isPrefixOf mod then
        throwError "joint occurrence audit imports numerical certificate {mod}"
  let ds := [``Math.CompactWeylHom.character,
    ``Math.CompactWeylHom.presents_of_characters,
    ``Math.CompactWeylHom.dimension, ``Math.CompactWeylHom.allowed_iff,
    ``Math.CompactWeylHom.equiv_iff,
    ``GUT.SMJointAlgebraicSupport.spin_formula, ``GUT.SMJointAlgebraicSupport.root_formula,
    ``GUT.SMJointAlgebraicSupport.terms_balance, ``GUT.SMJointAlgebraicSupport.occurs_iff,
    ``GUT.SMJointAlgebraicSupport.presents,
    ``GUT.SMJointAlgebraicSupport.local_allowed_iff,
    ``GUT.SMJointAlgebraicSupport.joint_allowed_iff,
    ``GUT.SMJointAlgebraicSupport.matches_iff, ``GUT.SMJointAlgebraicSupport.kernel_allowed_iff,
    ``GUT.SMJointAlgebraicSupport.ql_test_iff,
    ``GUT.SMJointAlgebraicSupport.original_ql_iff,
    ``GUT.SMJointAlgebraicSupport.original_ql_forbidden,
    ``GUT.SMJointColoredSupport.monomial_axis, ``GUT.SMJointColoredSupport.axis_evaluation,
    ``GUT.SMJointColoredSupport.target_continuous,
    ``GUT.SMJointColoredSupport.target_character, ``GUT.SMJointColoredSupport.target_evaluation,
    ``GUT.SMJointColoredSupport.reverse_evaluation, ``GUT.SMJointColoredSupport.presents,
    ``GUT.SMJointColoredSupport.joint_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "joint occurrence audit: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"joint occurrence audit: layer and {ds.length} strict transitive checks passed; Weyl consumers remain conditional"
