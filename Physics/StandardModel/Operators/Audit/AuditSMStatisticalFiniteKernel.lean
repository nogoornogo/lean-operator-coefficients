import Physics.StandardModel.Operators.SMQLPartialKernel
import Math.Audit.ImportOrigin
import Lean.Util.CollectAxioms

run_cmd do
  for mod in (← Lean.getEnv).header.moduleNames do
    if (`GUT).isPrefixOf mod then
      throwError "SM statistical finite kernel imports GUT application {mod}; original {SourceLayout.originalModule mod}"
  let ds := [``GUT.WeylRealTransvections.card_index,
    ``GUT.WeylRealTransvections.split_transvection,
    ``GUT.WeylRealTransvections.generates,
    ``GUT.WeylRealTransvections.spinor_affine,
    ``GUT.WeylRealTransvections.card_tests,
    ``GUT.WeylRealTransvections.exhaustive,
    ``GUT.SMWeylFiniteKernel.fieldDirection,
    ``GUT.SMWeylFiniteKernel.field_affine,
    ``GUT.SMWeylFiniteKernel.source_polynomial,
    ``GUT.SMWeylFiniteKernel.boson_fixed,
    ``GUT.SMWeylFiniteKernel.action_polynomial,
    ``GUT.SMWeylFiniteKernel.exhaustive,
    ``GUT.SMWeylFiniteKernel.coefficientEquiv,
    ``GUT.SMWeylFiniteKernel.allowed_iff_rank_lt,
    ``GUT.SMWeylFiniteKernel.basis,
    ``GUT.SMWeylFiniteKernel.canonicalEquiv,
    ``GUT.SMQLPartialKernel.coefficientEquiv,
    ``GUT.SMQLPartialKernel.local_allowed_iff,
    ``GUT.SMQLPartialKernel.original_allowed_iff]
  for d in ds do
    for ax in (← Lean.collectAxioms d) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "SM statistical finite kernel: {d} uses unexpected axiom {ax}"
  Lean.logInfo m!"SM statistical finite kernel: layer and {ds.length} strict transitive axiom checks passed"
